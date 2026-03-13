import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';

const schema = JSON.parse(
  readFileSync(resolve('schema/apache-license-cutover-approval-readiness-audit.schema.json'), 'utf8'),
);
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/legal/sample.apache-license-cutover-approval-readiness-audit.json'), 'utf8'),
);

const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const validate = ajv.compile(schema);

describe('apache-license-cutover-approval-readiness-audit contract', () => {
  it('accepts the sample fixture', () => {
    expect(validate(fixture)).toBe(true);
  });

  it('requires at least one approval item', () => {
    const invalid = structuredClone(fixture);
    invalid.approvalItems = [];
    expect(validate(invalid)).toBe(false);
    expect(validate.errors?.some((error) => error.instancePath === '/approvalItems')).toBe(true);
  });
});
