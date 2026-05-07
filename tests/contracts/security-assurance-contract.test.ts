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
  findings: loadJson('schema/security-finding-v1.schema.json'),
  review: loadJson('schema/security-review-v1.schema.json'),
};

const fixtures = {
  claims: loadJson('fixtures/security-assurance/sample.security-claims.json'),
  threatModel: loadJson('fixtures/security-assurance/sample.security-threat-model.json'),
  auditScope: loadJson('fixtures/security-assurance/sample.security-audit-scope.json'),
  findings: loadJson('fixtures/security-assurance/sample.security-findings.json'),
  review: loadJson('fixtures/security-assurance/sample.security-review.json'),
};

const buildValidator = (schema: JsonObject) => {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe('security assurance contracts', () => {
  it('validates the sample security assurance fixtures', () => {
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

  it('constrains threat model frameworks to represented STRIDE and CWE taxonomies', () => {
    const validate = buildValidator(schemas.threatModel);
    const invalidFixture = structuredClone(fixtures.threatModel) as {
      frameworks: string[];
    };

    invalidFixture.frameworks = ['STRIDE', 'OWASP_TOP_10'];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/frameworks/1')).toBe(true);
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

  it('keeps security findings connected to security claim ids', () => {
    const claimIds = new Set(
      (fixtures.claims.claims as Array<{ id: string }>).map((claim) => claim.id),
    );
    const findings = fixtures.findings.findings as Array<{ claimId: string }>;

    expect(findings).not.toHaveLength(0);
    for (const finding of findings) {
      expect(claimIds.has(finding.claimId)).toBe(true);
    }
  });

  it('distinguishes candidate findings from confirmed vulnerabilities', () => {
    const validate = buildValidator(schemas.findings);
    const validFixture = structuredClone(fixtures.findings) as {
      findings: Array<Record<string, unknown>>;
      summary: { byStatus: Record<string, number> };
    };

    validFixture.findings[0].status = 'confirmed';
    validFixture.summary.byStatus.candidate = 1;
    validFixture.summary.byStatus.confirmed = 1;

    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);

    validFixture.findings[0].status = 'vulnerable';
    expect(validate(validFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/findings/0/status')).toBe(true);
  });

  it('requires three-gate review results for every security review', () => {
    const validate = buildValidator(schemas.review);
    const invalidFixture = structuredClone(fixtures.review) as {
      reviews: Array<{ gates: Record<string, unknown> }>;
    };

    delete invalidFixture.reviews[0].gates.trustBoundary;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/reviews/0/gates')).toBe(true);
  });

  it('classifies false-positive root causes while allowing null for unresolved reviews', () => {
    const validate = buildValidator(schemas.review);
    const validFixture = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };

    expect(validFixture.reviews[0].falsePositiveRootCause).toBeNull();
    expect(validFixture.reviews[1].falsePositiveRootCause).toBe('out-of-scope');
    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);

    validFixture.reviews[1].falsePositiveRootCause = 'maybe-false-positive';
    expect(validate(validFixture)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath === '/reviews/1/falsePositiveRootCause'),
    ).toBe(true);
  });

  it('keeps security reviews connected to security finding ids', () => {
    const findingIds = new Set(
      (fixtures.findings.findings as Array<{ id: string }>).map((finding) => finding.id),
    );
    const reviews = fixtures.review.reviews as Array<{ findingId: string }>;

    expect(reviews).not.toHaveLength(0);
    for (const review of reviews) {
      expect(findingIds.has(review.findingId)).toBe(true);
    }
  });

});
