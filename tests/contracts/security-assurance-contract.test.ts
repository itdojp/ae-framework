import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import {
  validateSecurityAuditTaskBundleSemantics,
  validateSecurityCodeMapSemantics,
  validateSecurityFindingSemantics,
  validateSecurityReviewSemantics,
} from '../../scripts/ci/lib/security-assurance-contract.mjs';

type JsonObject = Record<string, unknown>;

const loadJson = (path: string) =>
  JSON.parse(readFileSync(resolve(path), 'utf8')) as JsonObject;

const schemas = {
  claims: loadJson('schema/security-claim-v1.schema.json'),
  threatModel: loadJson('schema/security-threat-model-v1.schema.json'),
  auditScope: loadJson('schema/security-audit-scope-v1.schema.json'),
  codeMap: loadJson('schema/security-code-map-v1.schema.json'),
  auditTasks: loadJson('schema/security-audit-task-bundle-v1.schema.json'),
  findings: loadJson('schema/security-finding-v1.schema.json'),
  review: loadJson('schema/security-review-v1.schema.json'),
};

const fixtures = {
  claims: loadJson('fixtures/security-assurance/sample.security-claims.json'),
  threatModel: loadJson('fixtures/security-assurance/sample.security-threat-model.json'),
  auditScope: loadJson('fixtures/security-assurance/sample.security-audit-scope.json'),
  codeMap: loadJson('fixtures/security-assurance/sample.security-code-map.json'),
  auditTasks: loadJson('fixtures/security-assurance/sample.security-audit-tasks.json'),
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

  it('keeps security code-map mappings connected to security claim ids', () => {
    const claimIds = new Set(
      (fixtures.claims.claims as Array<{ id: string }>).map((claim) => claim.id),
    );
    const mappings = fixtures.codeMap.mappings as Array<{ claimId: string; candidateLocations: unknown[] }>;

    expect(mappings).not.toHaveLength(0);
    for (const mapping of mappings) {
      expect(claimIds.has(mapping.claimId)).toBe(true);
      expect(Array.isArray(mapping.candidateLocations)).toBe(true);
    }
  });

  it('allows no-candidate security code-map entries with explicit warnings', () => {
    const validate = buildValidator(schemas.codeMap);
    const validFixture = structuredClone(fixtures.codeMap) as {
      mappings: Array<{
        candidateLocations: unknown[];
        coverage: string;
        warnings: Array<Record<string, unknown>>;
      }>;
      summary: {
        mappedClaims: number;
        totalCandidateLocations: number;
        totalWarnings: number;
        byCoverage: Record<string, number>;
      };
    };

    validFixture.mappings[0].candidateLocations = [];
    validFixture.mappings[0].coverage = 'none';
    validFixture.mappings[0].warnings = [
      {
        code: 'no-candidate-location',
        path: '/mappings/0/candidateLocations',
        message: 'No candidate source location was found for SEC-CLAIM-001.',
      },
    ];
    validFixture.summary.mappedClaims = 0;
    validFixture.summary.totalCandidateLocations = 0;
    validFixture.summary.totalWarnings = 1;
    validFixture.summary.byCoverage.none = 1;
    validFixture.summary.byCoverage.partial = 0;

    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);
  });


  it('keeps security audit tasks connected to security claim ids and code-map locations', () => {
    const claimIds = new Set(
      (fixtures.claims.claims as Array<{ id: string }>).map((claim) => claim.id),
    );
    const mappedClaimIds = new Set(
      (fixtures.codeMap.mappings as Array<{ claimId: string }>).map((mapping) => mapping.claimId),
    );
    const tasks = fixtures.auditTasks.tasks as Array<{ claimId: string; status: string; candidateLocations: unknown[] }>;

    expect(tasks).not.toHaveLength(0);
    for (const task of tasks) {
      expect(claimIds.has(task.claimId)).toBe(true);
      expect(mappedClaimIds.has(task.claimId)).toBe(true);
      expect(task.status).toBe('ready');
      expect(task.candidateLocations.length).toBeGreaterThan(0);
    }
  });

  it('enforces security audit task candidate location line ranges semantically', () => {
    const validFixture = structuredClone(fixtures.auditTasks);
    expect(validateSecurityAuditTaskBundleSemantics(validFixture)).toHaveLength(0);

    const invalidFixture = structuredClone(fixtures.auditTasks) as {
      tasks: Array<{ candidateLocations: Array<{ startLine: number; endLine: number }> }>;
    };
    invalidFixture.tasks[0].candidateLocations[0].startLine = 50;
    invalidFixture.tasks[0].candidateLocations[0].endLine = 10;

    expect(validateSecurityAuditTaskBundleSemantics(invalidFixture)).toEqual([
      expect.objectContaining({
        keyword: 'line_range_order',
        instancePath: '/tasks/0/candidateLocations/0/endLine',
      }),
    ]);
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

  it('preserves finding severity on security reviews when emitted by a producer', () => {
    const validate = buildValidator(schemas.review);
    const validFixture = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };

    expect(validFixture.reviews.map((review) => review.severity)).toEqual(['high', 'medium', 'low']);
    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);

    validFixture.reviews[0].severity = 'urgent';
    expect(validate(validFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/reviews/0/severity')).toBe(true);
  });

  it('classifies false-positive root causes while keeping them consistent with review results', () => {
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

    const unresolvedWithRootCause = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };
    unresolvedWithRootCause.reviews[0].falsePositiveRootCause = 'insufficient-evidence';
    expect(validate(unresolvedWithRootCause)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath === '/reviews/0/falsePositiveRootCause'),
    ).toBe(true);

    const confirmedWithRootCause = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };
    confirmedWithRootCause.reviews[0].result = 'confirmed';
    confirmedWithRootCause.reviews[0].falsePositiveRootCause = 'code-reading-error';
    expect(validate(confirmedWithRootCause)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath === '/reviews/0/falsePositiveRootCause'),
    ).toBe(true);

    const rejectedWithoutRootCause = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };
    rejectedWithoutRootCause.reviews[1].result = 'rejected';
    rejectedWithoutRootCause.reviews[1].falsePositiveRootCause = null;
    expect(validate(rejectedWithoutRootCause)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath === '/reviews/1/falsePositiveRootCause'),
    ).toBe(true);
  });

  it('enforces security finding affected location line ranges semantically', () => {
    const validFixture = structuredClone(fixtures.findings);
    expect(validateSecurityFindingSemantics(validFixture)).toHaveLength(0);

    const invalidFixture = structuredClone(fixtures.findings) as {
      findings: Array<{ affectedLocations: Array<{ startLine: number; endLine: number }> }>;
    };
    invalidFixture.findings[0].affectedLocations[0].startLine = 42;
    invalidFixture.findings[0].affectedLocations[0].endLine = 10;

    expect(validateSecurityFindingSemantics(invalidFixture)).toEqual([
      expect.objectContaining({
        keyword: 'line_range_order',
        instancePath: '/findings/0/affectedLocations/0/endLine',
      }),
    ]);
  });

  it('enforces security code-map candidate location line ranges semantically', () => {
    const validFixture = structuredClone(fixtures.codeMap);
    expect(validateSecurityCodeMapSemantics(validFixture)).toHaveLength(0);

    const invalidFixture = structuredClone(fixtures.codeMap) as {
      mappings: Array<{ candidateLocations: Array<{ startLine: number; endLine: number }> }>;
    };
    invalidFixture.mappings[0].candidateLocations[0].startLine = 50;
    invalidFixture.mappings[0].candidateLocations[0].endLine = 10;

    expect(validateSecurityCodeMapSemantics(invalidFixture)).toEqual([
      expect.objectContaining({
        keyword: 'line_range_order',
        instancePath: '/mappings/0/candidateLocations/0/endLine',
      }),
    ]);
  });

  it('enforces security review root-cause consistency semantically', () => {
    const validFixture = structuredClone(fixtures.review);
    expect(validateSecurityReviewSemantics(validFixture)).toHaveLength(0);

    const invalidFixture = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };
    invalidFixture.reviews[0].falsePositiveRootCause = 'insufficient-evidence';
    invalidFixture.reviews[1].falsePositiveRootCause = null;

    expect(validateSecurityReviewSemantics(invalidFixture)).toEqual([
      expect.objectContaining({
        keyword: 'false_positive_root_cause_result_mismatch',
        instancePath: '/reviews/0/falsePositiveRootCause',
      }),
      expect.objectContaining({
        keyword: 'false_positive_root_cause_missing',
        instancePath: '/reviews/1/falsePositiveRootCause',
      }),
    ]);
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
