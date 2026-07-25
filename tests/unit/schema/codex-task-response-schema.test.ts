import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';

const schemaPath = resolve('schema/codex-task-response.schema.json');
const validContinuePath = resolve('schema/examples/codex-task-response.unblocked.json');
const validBlockedPath = resolve('schema/examples/codex-task-response.blocked.json');
const invalidContinuePath = resolve('fixtures/codex/task-response.continue.invalid.json');

const loadJson = (filePath: string): unknown => JSON.parse(readFileSync(filePath, 'utf8'));

describe('codex-task-response schema contract', () => {
  const ajv = new Ajv2020({
    allErrors: true,
    strict: false,
  });
  const validate = ajv.compile(loadJson(schemaPath));

  it('accepts continue fixture with actionable nextActions', () => {
    const payload = loadJson(validContinuePath);
    expect(validate(payload)).toBe(true);
  });

  it('accepts blocked fixture with required human input metadata', () => {
    const payload = loadJson(validBlockedPath);
    expect(validate(payload)).toBe(true);
  });

  it('rejects continue fixture when nextActions is empty', () => {
    const payload = loadJson(invalidContinuePath);
    expect(validate(payload)).toBe(false);
    expect(validate.errors?.some((error) => error.keyword === 'minItems')).toBe(true);
  });

  it('rejects blocked fixture when nextActions is empty', () => {
    const payload = {
      ...(loadJson(validBlockedPath) as Record<string, unknown>),
      nextActions: [],
      warnings: ['REQUIRED_INPUT: provide missing blocked-context'],
    };
    expect(validate(payload)).toBe(false);
    expect(validate.errors?.some((error) => error.keyword === 'minItems')).toBe(true);
  });

  it('rejects blocked response when warnings is empty', () => {
    const payload = {
      ...(loadJson(validBlockedPath) as Record<string, unknown>),
      warnings: [],
    };
    expect(validate(payload)).toBe(false);
    expect(validate.errors?.some((error) => error.keyword === 'minItems')).toBe(true);
  });

  it('rejects response when nextActions or warnings includes empty string', () => {
    const blockedPayload = {
      ...(loadJson(validBlockedPath) as Record<string, unknown>),
      warnings: [''],
    };
    const continuePayload = {
      ...(loadJson(validContinuePath) as Record<string, unknown>),
      nextActions: [''],
    };
    const continuePayloadWithEmptyWarning = {
      ...(loadJson(validContinuePath) as Record<string, unknown>),
      warnings: [''],
    };

    expect(validate(blockedPayload)).toBe(false);
    expect(validate.errors?.some((error) => error.keyword === 'minLength')).toBe(true);
    expect(validate(continuePayload)).toBe(false);
    expect(validate.errors?.some((error) => error.keyword === 'minLength')).toBe(true);
    expect(validate(continuePayloadWithEmptyWarning)).toBe(false);
    expect(validate.errors?.some((error) => error.keyword === 'minLength')).toBe(true);
  });

  it('validates truthful formal artifact materialization parity', () => {
    const base = loadJson(validContinuePath) as Record<string, unknown>;
    const formal = {
      scaffold: {
        status: 'generated',
        artifactStatus: 'draft',
        validationStatus: 'valid',
        materializationStatus: 'partial',
        artifactPath: 'artifacts/codex/formal.tla',
        artifacts: [
          { kind: 'tla', required: true, status: 'written', path: 'artifacts/codex/formal.tla' },
          { kind: 'openapi', required: false, status: 'failed', message: 'OPENAPI artifact write failed (EISDIR)' },
        ],
      },
      modelChecking: {
        status: 'not-run',
        evidenceArtifact: null,
        runnerCommands: ['pnpm run verify:tla -- --engine=tlc'],
      },
    };
    expect(validate({ ...base, formal })).toBe(true);

    const nonexistentPathClaim = structuredClone(formal);
    (nonexistentPathClaim.scaffold.artifacts[1] as any).path = 'artifacts/codex/openapi.yaml';
    expect(validate({ ...base, formal: nonexistentPathClaim })).toBe(false);

    const missingWrittenPath = structuredClone(formal);
    delete (missingWrittenPath.scaffold.artifacts[0] as any).path;
    expect(validate({ ...base, formal: missingWrittenPath })).toBe(false);

    const missingScaffoldPath = structuredClone(formal);
    delete (missingScaffoldPath.scaffold as any).artifactPath;
    expect(validate({ ...base, formal: missingScaffoldPath })).toBe(false);

    const incorrectMaterializationStatus = structuredClone(formal);
    incorrectMaterializationStatus.scaffold.materializationStatus = 'written';
    expect(validate({ ...base, formal: incorrectMaterializationStatus })).toBe(false);
  });

  it('rejects mutations of per-artifact required flags', () => {
    const base = loadJson(validContinuePath) as Record<string, unknown>;
    const formal = {
      scaffold: {
        status: 'generated',
        artifactStatus: 'draft',
        validationStatus: 'valid',
        materializationStatus: 'written',
        artifactPath: 'artifacts/codex/formal.tla',
        artifacts: [
          { kind: 'tla', required: true, status: 'written', path: 'artifacts/codex/formal.tla' },
          { kind: 'openapi', required: false, status: 'written', path: 'artifacts/codex/openapi.yaml' },
        ],
      },
      modelChecking: {
        status: 'not-run',
        evidenceArtifact: null,
        runnerCommands: ['pnpm run verify:tla -- --engine=tlc'],
      },
    };
    expect(validate({ ...base, formal })).toBe(true);

    for (const [artifactIndex, mutatedRequired] of [[0, false], [1, true]] as const) {
      const mutation = structuredClone(formal);
      mutation.scaffold.artifacts[artifactIndex].required = mutatedRequired;
      expect(validate({ ...base, formal: mutation })).toBe(false);
      expect(validate.errors?.some((error) => error.keyword === 'const')).toBe(true);
    }

    const missingRequired = structuredClone(formal);
    delete (missingRequired.scaffold.artifacts[0] as any).required;
    expect(validate({ ...base, formal: missingRequired })).toBe(false);
    expect(validate.errors?.some((error) => error.keyword === 'required')).toBe(true);
  });

  it('allows no path or runner command when required TLA materialization fails', () => {
    const base = {
      ...(loadJson(validBlockedPath) as Record<string, unknown>),
      blockingReason: 'formal-primary-artifact-materialization-failed',
      requiredHumanInput: 'writable repository-local output for required TLA artifact materialization',
    };
    const formal = {
      scaffold: {
        status: 'generated',
        artifactStatus: 'draft',
        validationStatus: 'valid',
        materializationStatus: 'partial',
        artifacts: [
          { kind: 'tla', required: true, status: 'failed', message: 'TLA artifact write failed (EISDIR)' },
          { kind: 'openapi', required: false, status: 'written', path: 'artifacts/codex/openapi.yaml' },
        ],
      },
      modelChecking: {
        status: 'not-run',
        evidenceArtifact: null,
        runnerCommands: [] as string[],
      },
    };
    expect(validate({ ...base, formal })).toBe(true);

    const nonexistentScaffoldPath = structuredClone(formal);
    (nonexistentScaffoldPath.scaffold as any).artifactPath = 'artifacts/codex/formal.tla';
    expect(validate({ ...base, formal: nonexistentScaffoldPath })).toBe(false);

    const commandWithoutTla = structuredClone(formal);
    commandWithoutTla.modelChecking.runnerCommands.push('pnpm run verify:tla -- --engine=tlc');
    expect(validate({ ...base, formal: commandWithoutTla })).toBe(false);

    expect(validate({ ...base, shouldBlockProgress: false, formal })).toBe(false);
    expect(validate({ ...base, blockingReason: 'formal-artifact-materialization-failed', formal })).toBe(false);
  });
});
