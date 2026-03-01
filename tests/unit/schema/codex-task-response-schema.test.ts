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
});
