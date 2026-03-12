import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/quality-scorecard.schema.json'), 'utf8'),
) as Record<string, unknown>;
const metadataSchema = JSON.parse(
  readFileSync(resolve('schema/artifact-metadata.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/quality/sample.quality-scorecard.json'), 'utf8'),
) as Record<string, unknown>;

describe('quality-scorecard contract', () => {
  it('validates the sample quality scorecard fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    ajv.addSchema(metadataSchema);
    const validate = ajv.compile(schema);

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects payloads without contractId', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    ajv.addSchema(metadataSchema);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as { contractId?: string };

    delete invalidFixture.contractId;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '')).toBe(true);
  });

  it('rejects required inputs marked missing', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    ajv.addSchema(metadataSchema);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      inputs: {
        verifyLiteSummary: {
          path: string | null;
          present: boolean;
          required: boolean;
        };
      };
    };

    invalidFixture.inputs.verifyLiteSummary = {
      path: null,
      present: false,
      required: true,
    };

    expect(validate(invalidFixture)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath.startsWith('/inputs/verifyLiteSummary')),
    ).toBe(true);
  });
});
