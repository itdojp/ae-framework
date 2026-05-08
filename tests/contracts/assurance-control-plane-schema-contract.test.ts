import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const loadJson = (path: string) => JSON.parse(readFileSync(resolve(path), 'utf8')) as Record<string, unknown>;

const buildValidator = (schemaPath: string) => {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(loadJson(schemaPath));
};

describe('assurance control plane preview schema contracts', () => {
  it('validates the claim-level summary fixture with all preview states', () => {
    const validate = buildValidator('schema/claim-level-summary-v1.schema.json');
    const fixture = loadJson('fixtures/assurance/sample.claim-level-summary-v1.json') as {
      claims: Array<{ state: string }>;
    };

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
    expect(fixture.claims.map((claim) => claim.state)).toEqual([
      'satisfied',
      'tested',
      'model-checked',
      'proved',
      'runtime-mitigated',
      'waived',
      'unresolved',
      'failed',
      'not-applicable',
    ]);
  });

  it('rejects an enforced claim-level decision without a reason', () => {
    const validate = buildValidator('schema/claim-level-summary-v1.schema.json');
    const invalidFixture = loadJson('fixtures/assurance/invalid.claim-level-summary-v1.missing-enforced-reason.json');

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0/decision')).toBe(true);
  });

  it('rejects waived claim-level summaries without waiver references', () => {
    const validate = buildValidator('schema/claim-level-summary-v1.schema.json');
    const invalidFixture = structuredClone(loadJson('fixtures/assurance/sample.claim-level-summary-v1.json')) as {
      claims: Array<Record<string, unknown>>;
    };
    const waivedClaim = invalidFixture.claims.find((claim) => claim.state === 'waived');
    if (!waivedClaim) {
      throw new Error('sample fixture must include a waived claim');
    }
    waivedClaim.waiverRefs = [];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath.endsWith('/waiverRefs'))).toBe(true);
  });

  it('requires applicability metadata for not-applicable claim-level summaries', () => {
    const validate = buildValidator('schema/claim-level-summary-v1.schema.json');
    const invalidFixture = structuredClone(loadJson('fixtures/assurance/sample.claim-level-summary-v1.json')) as {
      claims: Array<Record<string, unknown>>;
    };
    const notApplicableClaim = invalidFixture.claims.find((claim) => claim.state === 'not-applicable');
    if (!notApplicableClaim) {
      throw new Error('sample fixture must include a not-applicable claim');
    }
    delete notApplicableClaim.applicability;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/8')).toBe(true);
  });

  it('validates the temporary override fixture', () => {
    const validate = buildValidator('schema/temporary-override-v1.schema.json');
    const fixture = loadJson('fixtures/assurance/sample.temporary-override-v1.json');

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects temporary overrides without evidence links', () => {
    const validate = buildValidator('schema/temporary-override-v1.schema.json');
    const invalidFixture = loadJson('fixtures/assurance/invalid.temporary-override-v1.missing-evidence-link.json');

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '')).toBe(true);
  });

  it('rejects temporary overrides without related claim ids', () => {
    const validate = buildValidator('schema/temporary-override-v1.schema.json');
    const invalidFixture = structuredClone(loadJson('fixtures/assurance/sample.temporary-override-v1.json')) as {
      relatedClaimIds: string[];
    };
    invalidFixture.relatedClaimIds = [];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/relatedClaimIds')).toBe(true);
  });
});
