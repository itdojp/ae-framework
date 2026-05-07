import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

type JsonObject = Record<string, unknown>;

const loadJson = (path: string) =>
  JSON.parse(readFileSync(resolve(path), 'utf8')) as JsonObject;

const schemas = {
  claims: loadJson('schema/security-claim-v1.schema.json'),
  threatModel: loadJson('schema/security-threat-model-v1.schema.json'),
  auditScope: loadJson('schema/security-audit-scope-v1.schema.json'),
};

const fixtures = {
  claims: loadJson('fixtures/security-assurance/sample.security-claims.json'),
  threatModel: loadJson('fixtures/security-assurance/sample.security-threat-model.json'),
  auditScope: loadJson('fixtures/security-assurance/sample.security-audit-scope.json'),
};

const buildValidator = (schema: JsonObject) => {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe('security assurance contracts', () => {
  it('validates the sample security claim, threat model, and audit scope fixtures', () => {
    for (const [name, schema] of Object.entries(schemas)) {
      const validate = buildValidator(schema);
      const fixture = fixtures[name as keyof typeof fixtures];

      expect(validate(fixture), `${name}: ${JSON.stringify(validate.errors)}`).toBe(true);
    }
  });

  it('requires security claims to carry the fields needed by downstream artifacts', () => {
    const validate = buildValidator(schemas.claims);
    const invalidFixture = structuredClone(fixtures.claims) as {
      claims: Array<Record<string, unknown>>;
    };

    delete invalidFixture.claims[0].sourceRefs;
    delete invalidFixture.claims[0].threatTags;
    delete invalidFixture.claims[0].trustBoundary;
    delete invalidFixture.claims[0].requiredLanes;
    delete invalidFixture.claims[0].provenance;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0')).toBe(true);
  });

  it('allows the MVP security claim type set required by #3258', () => {
    const validate = buildValidator(schemas.claims);
    const validFixture = structuredClone(fixtures.claims) as {
      claims: Array<Record<string, unknown>>;
      summary: { totalClaims: number; byCriticality: Record<string, number> };
    };

    const baseClaim = validFixture.claims[0];
    validFixture.claims = ['invariant', 'precondition', 'postcondition', 'assumption'].map(
      (type, index) => ({
        ...baseClaim,
        id: `SEC-CLAIM-TYPE-${index + 1}`,
        type,
      }),
    );
    validFixture.summary.totalClaims = validFixture.claims.length;
    validFixture.summary.byCriticality.high = validFixture.claims.length;

    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects unsupported security claim types', () => {
    const validate = buildValidator(schemas.claims);
    const invalidFixture = structuredClone(fixtures.claims) as {
      claims: Array<Record<string, unknown>>;
    };

    invalidFixture.claims[0].type = 'vulnerability';

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0/type')).toBe(true);
  });

  it('keeps threat model claim references aligned with the security claim fixture', () => {
    const claimIds = new Set(
      ((fixtures.claims.claims as Array<{ id: string }>)).map((claim) => claim.id),
    );
    const threats = fixtures.threatModel.threats as Array<{ relatedClaimIds: string[] }>;

    expect(threats).not.toHaveLength(0);
    for (const threat of threats) {
      expect(threat.relatedClaimIds.every((claimId) => claimIds.has(claimId))).toBe(true);
    }
  });

  it('requires the audit scope to include at least one in-scope glob', () => {
    const validate = buildValidator(schemas.auditScope);
    const invalidFixture = structuredClone(fixtures.auditScope) as {
      inScope: string[];
    };

    invalidFixture.inScope = [];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/inScope')).toBe(true);
  });
});
