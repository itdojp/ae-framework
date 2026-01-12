import { readFileSync } from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

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
addFormats(ajv);

let cachedValidator: ReturnType<typeof ajv.compile> | null = null;

function loadSchema() {
  const schemaPath = path.resolve(process.cwd(), 'schema/state-machine.schema.json');
  return JSON.parse(readFileSync(schemaPath, 'utf8'));
}

function getValidator() {
  if (!cachedValidator) {
    cachedValidator = ajv.compile(loadSchema());
  }
  return cachedValidator;
}

function countSummary(machine: any): StateMachineSummary {
  const states = Array.isArray(machine?.states) ? machine.states.length : 0;
  const events = Array.isArray(machine?.events) ? machine.events.length : 0;
  const transitions = Array.isArray(machine?.transitions) ? machine.transitions.length : 0;
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

export function validateStateMachineDefinition(data: unknown): StateMachineValidationResult {
  const issues: StateMachineIssue[] = [];
  const summary = countSummary(data);
  const validate = getValidator();
  const schemaOk = validate(data);

  if (!schemaOk) {
    for (const error of validate.errors ?? []) {
      issues.push({
        code: 'SCHEMA_INVALID',
        severity: 'error',
        message: error.message ?? 'Schema validation failed',
        location: { jsonPointer: error.instancePath || error.schemaPath }
      });
    }
    return { ok: false, issues, summary };
  }

  const machine = data as any;
  const stateNames = Array.isArray(machine.states)
    ? machine.states.map((state: any) => state?.name).filter(Boolean)
    : [];
  const eventNames = Array.isArray(machine.events)
    ? machine.events.filter((event: any) => typeof event === 'string')
    : [];

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
