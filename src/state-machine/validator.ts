import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Ajv2020, type ErrorObject, type ValidateFunction } from 'ajv/dist/2020.js';
import type { StateMachineDefinition } from './types.js';

export type StateMachineIssueSeverity = 'error' | 'warn';

export interface StateMachineIssue {
  code: string;
  severity: StateMachineIssueSeverity;
  message: string;
  location?: { jsonPointer?: string };
}

export interface StateMachineSummary {
  states: number;
  events: number;
  transitions: number;
}

export interface StateMachineValidationResult {
  ok: boolean;
  issues: StateMachineIssue[];
  summary: StateMachineSummary;
}

const ajv = new Ajv2020({ allErrors: true, strict: false });

let cachedValidator: ValidateFunction<unknown> | undefined;
let metaSchemasRegistered = false;

function resolveSchemaPath() {
  const cwdPath = path.resolve(process.cwd(), 'schema/state-machine.schema.json');
  const modulePath = path.resolve(
    path.dirname(fileURLToPath(import.meta.url)),
    '../../schema/state-machine.schema.json'
  );
  const packageRootPath = path.resolve(
    path.dirname(fileURLToPath(import.meta.url)),
    '../../../schema/state-machine.schema.json'
  );
  const candidates = [cwdPath, modulePath, packageRootPath];
  const resolved = candidates.find((candidate) => existsSync(candidate));
  if (!resolved) {
    throw new Error(`State machine schema not found. Looked in: ${candidates.join(', ')}`);
  }
  return resolved;
}

function loadSchema() {
  const schemaPath = resolveSchemaPath();
  const schema = JSON.parse(readFileSync(schemaPath, 'utf8')) as Record<string, unknown>;
  return schema;
}

function ensure2020MetaSchemas() {
  if (metaSchemasRegistered) {
    return;
  }
  // Ajv2020 registers the default 2020-12 meta schema on construction.
  metaSchemasRegistered = true;
}

function getValidator(): ValidateFunction<unknown> {
  if (!cachedValidator) {
    ensure2020MetaSchemas();
    const schema = loadSchema();
    const schemaId = typeof schema['$id'] === 'string' ? schema['$id'] : undefined;
    const existing = schemaId ? ajv.getSchema(schemaId) : undefined;
    cachedValidator = (existing ?? ajv.compile(schema)) as ValidateFunction<unknown>;
  }
  return cachedValidator;
}

function countSummary(machine: unknown): StateMachineSummary {
  if (!machine || typeof machine !== 'object') {
    return { states: 0, events: 0, transitions: 0 };
  }
  const candidate = machine as Partial<StateMachineDefinition>;
  const states = Array.isArray(candidate.states) ? candidate.states.length : 0;
  const events = Array.isArray(candidate.events) ? candidate.events.length : 0;
  const transitions = Array.isArray(candidate.transitions) ? candidate.transitions.length : 0;
  return { states, events, transitions };
}

function collectDuplicates(values: string[]) {
  const seen = new Set<string>();
  const duplicates = new Set<string>();
  for (const value of values) {
    if (seen.has(value)) {
      duplicates.add(value);
    }
    seen.add(value);
  }
  return Array.from(duplicates);
}

/**
 * Validate a state machine definition against the schema and semantic rules.
 */
export function validateStateMachineDefinition(data: unknown): StateMachineValidationResult {
  const issues: StateMachineIssue[] = [];
  const summary = countSummary(data);
  const validate = getValidator();
  const schemaOk = validate(data);

  if (!schemaOk) {
    const errors = (validate.errors ?? []) as ErrorObject[];
    for (const error of errors) {
      issues.push({
        code: 'SCHEMA_INVALID',
        severity: 'error',
        message: error.message ?? 'Schema validation failed',
        location: { jsonPointer: error.instancePath || error.schemaPath }
      });
    }
    return { ok: false, issues, summary };
  }

  const machine = data as StateMachineDefinition;
  const stateNames = Array.isArray(machine.states)
    ? machine.states
        .map((state) => state?.name)
        .filter((name): name is string => typeof name === 'string')
    : [];
  const eventNames = Array.isArray(machine.events)
    ? machine.events.filter((event): event is string => typeof event === 'string')
    : [];

  for (const [index, name] of stateNames.entries()) {
    if (!name.trim()) {
      issues.push({
        code: 'EMPTY_STATE_NAME',
        severity: 'error',
        message: 'State name must be a non-empty string',
        location: { jsonPointer: `/states/${index}/name` }
      });
    }
  }

  for (const [index, name] of eventNames.entries()) {
    if (!name.trim()) {
      issues.push({
        code: 'EMPTY_EVENT_NAME',
        severity: 'error',
        message: 'Event name must be a non-empty string',
        location: { jsonPointer: `/events/${index}` }
      });
    }
  }

  for (const name of collectDuplicates(stateNames)) {
    issues.push({
      code: 'DUPLICATE_STATE',
      severity: 'error',
      message: `Duplicate state: ${name}`,
      location: { jsonPointer: '/states' }
    });
  }

  for (const name of collectDuplicates(eventNames)) {
    issues.push({
      code: 'DUPLICATE_EVENT',
      severity: 'error',
      message: `Duplicate event: ${name}`,
      location: { jsonPointer: '/events' }
    });
  }

  if (!stateNames.includes(machine.initial)) {
    issues.push({
      code: 'INITIAL_NOT_FOUND',
      severity: 'error',
      message: `Initial state not found: ${machine.initial}`,
      location: { jsonPointer: '/initial' }
    });
  }

  const transitions = Array.isArray(machine.transitions) ? machine.transitions : [];
  const transitionKeys = new Map<string, number>();
  for (const [index, transition] of transitions.entries()) {
    if (!stateNames.includes(transition.from)) {
      issues.push({
        code: 'UNDEFINED_STATE_REF',
        severity: 'error',
        message: `Transition references missing state: ${transition.from}`,
        location: { jsonPointer: `/transitions/${index}/from` }
      });
    }

    if (!stateNames.includes(transition.to)) {
      issues.push({
        code: 'UNDEFINED_STATE_REF',
        severity: 'error',
        message: `Transition references missing state: ${transition.to}`,
        location: { jsonPointer: `/transitions/${index}/to` }
      });
    }

    if (!eventNames.includes(transition.event)) {
      issues.push({
        code: 'UNDEFINED_EVENT_REF',
        severity: 'error',
        message: `Transition references missing event: ${transition.event}`,
        location: { jsonPointer: `/transitions/${index}/event` }
      });
    }

    const key = `${transition.from}::${transition.event}::${transition.guard ?? ''}`;
    if (transitionKeys.has(key)) {
      issues.push({
        code: 'AMBIGUOUS_TRANSITION',
        severity: 'error',
        message: `Duplicate transition for ${transition.from}/${transition.event}`,
        location: { jsonPointer: `/transitions/${index}` }
      });
    }
    transitionKeys.set(key, index);
  }

  return { ok: issues.length === 0, issues, summary };
}
