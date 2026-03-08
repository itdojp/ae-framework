import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const assuranceProfileSchema = JSON.parse(
  readFileSync(resolve('schema/assurance-profile.schema.json'), 'utf8'),
) as Record<string, unknown>;
const assuranceProfileFixture = JSON.parse(
  readFileSync(resolve('fixtures/assurance/sample.assurance-profile.json'), 'utf8'),
) as Record<string, unknown>;

describe('assurance profile contract', () => {
  it('validates the sample assurance profile fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);

    expect(validate(assuranceProfileFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects claims without required evidence kinds', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);
    const invalidFixture = structuredClone(assuranceProfileFixture) as {
      claims: Array<Record<string, unknown>>;
    };

    invalidFixture.claims[0] = {
      ...invalidFixture.claims[0],
      requiredEvidenceKinds: [],
    };

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0/requiredEvidenceKinds')).toBe(true);
  });

  it('rejects claims with non-positive minIndependentSources', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);
    const invalidFixture = structuredClone(assuranceProfileFixture) as {
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
