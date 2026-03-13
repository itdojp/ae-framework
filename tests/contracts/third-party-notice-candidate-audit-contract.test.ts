import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/third-party-notice-candidate-audit.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/legal/sample.third-party-notice-candidate-audit.json'), 'utf8'),
) as Record<string, unknown>;

describe('third-party notice candidate audit contract', () => {
  it('validates the sample fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects missing vendor-like segments', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      inputs: { vendorLikeSegments?: string[] };
    };

    delete invalidFixture.inputs.vendorLikeSegments;

    expect(validate(invalidFixture)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath === '/inputs'),
    ).toBe(true);
  });
});
