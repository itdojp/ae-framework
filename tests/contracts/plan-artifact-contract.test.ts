import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';

const schema = JSON.parse(readFileSync(resolve('schema/plan-artifact.schema.json'), 'utf8'));
const fixture = JSON.parse(readFileSync(resolve('fixtures/plan/sample.plan-artifact.json'), 'utf8'));

describe('plan-artifact contract', () => {
  it('accepts the sample fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    expect(validate(fixture)).toBe(true);
  });

  it('rejects missing verificationPlan', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalid = structuredClone(fixture);
    delete invalid.verificationPlan;
    expect(validate(invalid)).toBe(false);
  });
});
