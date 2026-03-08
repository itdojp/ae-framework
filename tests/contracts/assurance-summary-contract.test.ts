import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const artifactMetadataSchema = JSON.parse(
  readFileSync(resolve('schema/artifact-metadata.schema.json'), 'utf8'),
) as Record<string, unknown>;
const assuranceSummarySchema = JSON.parse(
  readFileSync(resolve('schema/assurance-summary.schema.json'), 'utf8'),
) as Record<string, unknown>;
const assuranceSummaryFixture = JSON.parse(
  readFileSync(resolve('fixtures/assurance/sample.assurance-summary.json'), 'utf8'),
) as Record<string, unknown>;

const buildValidator = () => {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  ajv.addSchema(artifactMetadataSchema);
  return ajv.compile(assuranceSummarySchema);
};

describe('assurance summary contract', () => {
  it('validates the sample assurance summary fixture', () => {
    const validate = buildValidator();

    expect(validate(assuranceSummaryFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects claims without minIndependentSources', () => {
    const validate = buildValidator();
    const invalidFixture = structuredClone(assuranceSummaryFixture) as {
      claims: Array<Record<string, unknown>>;
    };

    invalidFixture.claims[0] = {
      ...invalidFixture.claims[0],
      minIndependentSources: 0,
    };

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0/minIndependentSources')).toBe(true);
  });
});
