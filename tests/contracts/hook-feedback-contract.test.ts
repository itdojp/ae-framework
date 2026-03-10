import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/hook-feedback.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/agents/sample.hook-feedback.json'), 'utf8'),
) as Record<string, unknown>;
const partialFixture = JSON.parse(
  readFileSync(resolve('fixtures/agents/sample.hook-feedback-partial.json'), 'utf8'),
) as Record<string, unknown>;

describe('hook-feedback contract', () => {
  it('validates the sample hook feedback fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('validates the partial-input hook feedback fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(partialFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects blocked feedback without blocking reasons', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      status: string;
      blockingReasons: unknown[];
    };

    invalidFixture.status = 'blocked';
    invalidFixture.blockingReasons = [];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/blockingReasons')).toBe(true);
  });

  it('keeps v1 source assurance and ui e2e paths optional', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const legacyFixture = structuredClone(fixture) as {
      source: Record<string, unknown>;
    };

    delete legacyFixture.source.assuranceSummaryPath;
    delete legacyFixture.source.uiE2ESummaryPath;

    expect(validate(legacyFixture), JSON.stringify(validate.errors)).toBe(true);
  });
});
