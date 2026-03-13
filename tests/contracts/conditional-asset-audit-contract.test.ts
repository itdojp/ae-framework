import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/conditional-asset-audit.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/legal/sample.conditional-asset-audit.json'), 'utf8'),
) as Record<string, unknown>;

describe('conditional asset audit contract', () => {
  it('validates the sample fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects invalid originClass values', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      items: Array<{ originClass: string }>;
    };
    invalidFixture.items[0].originClass = 'unknown-origin-class';
    expect(validate(invalidFixture)).toBe(false);
  });
});
