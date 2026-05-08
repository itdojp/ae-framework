import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import {
  validateSecurityAuditTaskBundleSemantics,
  validateSecurityAuditPromptPackSemantics,
  validateSecurityCodeMapSemantics,
  validateSecurityEntrypointMapSemantics,
  validateSecurityFindingSemantics,
  validateSecurityReviewSemantics,
  validateSymbolIndexSemantics,
} from '../../scripts/ci/lib/security-assurance-contract.mjs';

type JsonObject = Record<string, unknown>;

const loadJson = (path: string) =>
  JSON.parse(readFileSync(resolve(path), 'utf8')) as JsonObject;

const schemas = {
  claims: loadJson('schema/security-claim-v1.schema.json'),
  threatModel: loadJson('schema/security-threat-model-v1.schema.json'),
  auditScope: loadJson('schema/security-audit-scope-v1.schema.json'),
  codeMap: loadJson('schema/security-code-map-v1.schema.json'),
  symbolIndex: loadJson('schema/symbol-index-v1.schema.json'),
  entrypointMap: loadJson('schema/security-entrypoint-map-v1.schema.json'),
  auditTasks: loadJson('schema/security-audit-task-bundle-v1.schema.json'),
  auditPromptPack: loadJson('schema/security-audit-prompt-pack-v1.schema.json'),
  findings: loadJson('schema/security-finding-v1.schema.json'),
  review: loadJson('schema/security-review-v1.schema.json'),
};

const fixtures = {
  claims: loadJson('fixtures/security-assurance/sample.security-claims.json'),
  threatModel: loadJson('fixtures/security-assurance/sample.security-threat-model.json'),
  auditScope: loadJson('fixtures/security-assurance/sample.security-audit-scope.json'),
  codeMap: loadJson('fixtures/security-assurance/sample.security-code-map.json'),
  symbolIndex: loadJson('fixtures/security-assurance/sample.symbol-index.json'),
  entrypointMap: loadJson('fixtures/security-assurance/sample.security-entrypoint-map.json'),
  auditTasks: loadJson('fixtures/security-assurance/sample.security-audit-tasks.json'),
  auditPromptPack: loadJson('fixtures/security-assurance/sample.security-audit-prompt-pack.json'),
  findings: loadJson('fixtures/security-assurance/sample.security-findings.json'),
  review: loadJson('fixtures/security-assurance/sample.security-review.json'),
};

const boundaryFixtures = {
  multipleReviewRecords: loadJson('fixtures/security-assurance/boundary-cases/multiple-review-records.security-review.json'),
  trustBoundaryUnknown: loadJson('fixtures/security-assurance/boundary-cases/trust-boundary-unknown.security-review.json'),
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

  it('allows security code-map summary to record optional symbol-index provenance', () => {
    const validate = buildValidator(schemas.codeMap);
    const validFixture = structuredClone(fixtures.codeMap) as {
      summary: Record<string, unknown>;
      provenance: Record<string, unknown>;
    };

    validFixture.summary.symbolIndex = {
      used: true,
      input: 'fixtures/security-assurance/sample.symbol-index.json',
      totalSymbols: 1,
      inScopeSymbols: 1,
      matchedSymbols: 1,
      fallbackClaims: 0,
    };
    validFixture.provenance.symbolIndex = 'fixtures/security-assurance/sample.symbol-index.json';

    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('enforces symbol-index semantic line ranges and unique ids', () => {
    const validFixture = structuredClone(fixtures.symbolIndex);
    expect(validateSymbolIndexSemantics(validFixture)).toHaveLength(0);

    const invalidFixture = structuredClone(fixtures.symbolIndex) as {
      symbols: Array<{ id: string; startLine: number; endLine: number }>;
    };
    invalidFixture.symbols.push({
      ...invalidFixture.symbols[0],
      id: invalidFixture.symbols[0].id,
      startLine: 50,
      endLine: 10,
    });

    expect(validateSymbolIndexSemantics(invalidFixture)).toEqual([
      expect.objectContaining({
        keyword: 'line_range_order',
        instancePath: '/symbols/1/endLine',
      }),
      expect.objectContaining({
        keyword: 'duplicate_symbol_id',
        instancePath: '/symbols/1/id',
      }),
    ]);
  });

  it('enforces security-entrypoint-map semantic line ranges, unique ids, and summary counts', () => {
    const validFixture = structuredClone(fixtures.entrypointMap);
    expect(validateSecurityEntrypointMapSemantics(validFixture)).toHaveLength(0);

    const invalidFixture = structuredClone(fixtures.entrypointMap) as {
      entrypoints: Array<{
        id: string;
        startLine: number;
        endLine: number;
        reaches: Array<{ startLine: number; endLine: number }>;
      }>;
      summary: {
        totalEntrypoints: number;
        attackerControlledEntrypoints: number;
        totalReachableLocations: number;
      };
    };
    invalidFixture.entrypoints.push({
      ...invalidFixture.entrypoints[0],
      id: invalidFixture.entrypoints[0].id,
      startLine: 80,
      endLine: 10,
      reaches: [
        {
          ...invalidFixture.entrypoints[0].reaches[0],
          startLine: 30,
          endLine: 10,
        },
      ],
    });
    invalidFixture.summary.totalEntrypoints = 1;
    invalidFixture.summary.attackerControlledEntrypoints = 1;
    invalidFixture.summary.totalReachableLocations = 1;

    expect(validateSecurityEntrypointMapSemantics(invalidFixture)).toEqual([
      expect.objectContaining({
        keyword: 'line_range_order',
        instancePath: '/entrypoints/1/endLine',
      }),
      expect.objectContaining({
        keyword: 'line_range_order',
        instancePath: '/entrypoints/1/reaches/0/endLine',
      }),
      expect.objectContaining({
        keyword: 'duplicate_entrypoint_id',
        instancePath: '/entrypoints/1/id',
      }),
      expect.objectContaining({
        keyword: 'summary_total_entrypoints_mismatch',
        instancePath: '/summary/totalEntrypoints',
      }),
      expect.objectContaining({
        keyword: 'summary_attacker_controlled_entrypoints_mismatch',
        instancePath: '/summary/attackerControlledEntrypoints',
      }),
      expect.objectContaining({
        keyword: 'summary_total_reachable_locations_mismatch',
        instancePath: '/summary/totalReachableLocations',
      }),
    ]);
  });

  it('allows security-entrypoint-map reaches to omit line ranges when path and symbol evidence is available', () => {
    const validate = buildValidator(schemas.entrypointMap);
    const validFixture = structuredClone(fixtures.entrypointMap) as {
      entrypoints: Array<{ reaches: Array<Record<string, unknown>> }>;
    };

    delete validFixture.entrypoints[0].reaches[0].startLine;
    delete validFixture.entrypoints[0].reaches[0].endLine;

    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateSecurityEntrypointMapSemantics(validFixture)).toHaveLength(0);
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

  it('keeps security audit prompt packs connected to generated prompt paths and candidate locations', () => {
    const validate = buildValidator(schemas.auditPromptPack);
    const validFixture = structuredClone(fixtures.auditPromptPack);

    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateSecurityAuditPromptPackSemantics(validFixture)).toHaveLength(0);

    const tasks = validFixture.tasks as Array<{
      taskId: string;
      claimId: string;
      promptPath: string;
      status: string;
      candidateLocations: unknown[];
    }>;
    expect(tasks).not.toHaveLength(0);
    expect(tasks[0]).toMatchObject({
      taskId: 'SEC-AUDIT-TASK-001',
      claimId: 'SEC-CLAIM-001',
      status: 'ready',
      promptPath: 'artifacts/security/codex-audit-prompts/prompts/SEC-AUDIT-TASK-001.md',
    });
    expect(tasks[0].candidateLocations.length).toBeGreaterThan(0);
  });

  it('enforces security audit prompt pack semantic summary and path invariants', () => {
    const invalidSummary = structuredClone(fixtures.auditPromptPack) as {
      summary: { readyTasks: number };
    };
    invalidSummary.summary.readyTasks = 0;

    expect(validateSecurityAuditPromptPackSemantics(invalidSummary)).toEqual([
      expect.objectContaining({
        keyword: 'summary_count_mismatch',
        instancePath: '/summary/readyTasks',
      }),
    ]);

    const duplicatePath = structuredClone(fixtures.auditPromptPack) as {
      tasks: Array<Record<string, unknown>>;
      summary: Record<string, unknown>;
    };
    duplicatePath.tasks.push({ ...duplicatePath.tasks[0], taskId: 'SEC-AUDIT-TASK-002' });
    duplicatePath.summary.totalTasks = 2;
    duplicatePath.summary.readyTasks = 2;
    duplicatePath.summary.totalCandidateLocations = 2;

    expect(validateSecurityAuditPromptPackSemantics(duplicatePath)).toEqual([
      expect.objectContaining({
        keyword: 'duplicate_prompt_path',
        instancePath: '/tasks/1/promptPath',
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

  it('allows claim type-aware assumption handling on security reviews', () => {
    const validate = buildValidator(schemas.review);
    const validFixture = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };

    validFixture.reviews[0].claimId = 'SEC-CLAIM-001';
    validFixture.reviews[0].claimType = 'assumption';
    validFixture.reviews[0].assumptionHandling = {
      mode: 'assumption-validation-required',
      rationale: 'Validate the assumption before treating this candidate as a vulnerability.',
      evidenceRefs: ['SEC-CLAIM-001', 'SEC-FINDING-001'],
    };

    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateSecurityReviewSemantics(validFixture)).toHaveLength(0);

    const missingHandling = structuredClone(validFixture);
    delete missingHandling.reviews[0].assumptionHandling;
    expect(validate(missingHandling)).toBe(false);
    expect(validateSecurityReviewSemantics(missingHandling)).toEqual([
      expect.objectContaining({
        keyword: 'assumption_handling_missing',
        instancePath: '/reviews/0/assumptionHandling',
      }),
    ]);

    const nonAssumptionWithHandling = structuredClone(validFixture);
    nonAssumptionWithHandling.reviews[0].claimType = 'invariant';
    expect(validate(nonAssumptionWithHandling), JSON.stringify(validate.errors)).toBe(true);
    expect(validateSecurityReviewSemantics(nonAssumptionWithHandling)).toEqual([
      expect.objectContaining({
        keyword: 'assumption_handling_without_assumption',
        instancePath: '/reviews/0/assumptionHandling',
      }),
    ]);
  });

  it('requires claimId and claimType to be emitted together on security reviews', () => {
    const validate = buildValidator(schemas.review);
    const claimTypeOnly = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };
    claimTypeOnly.reviews[0].claimType = 'invariant';

    expect(validate(claimTypeOnly)).toBe(false);
    expect(validateSecurityReviewSemantics(claimTypeOnly)).toEqual([
      expect.objectContaining({
        keyword: 'claim_id_missing_for_claim_type',
        instancePath: '/reviews/0/claimId',
      }),
    ]);

    const claimIdOnly = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };
    claimIdOnly.reviews[0].claimId = 'SEC-CLAIM-001';

    expect(validate(claimIdOnly)).toBe(false);
    expect(validateSecurityReviewSemantics(claimIdOnly)).toEqual([
      expect.objectContaining({
        keyword: 'claim_type_missing_for_claim_id',
        instancePath: '/reviews/0/claimType',
      }),
    ]);
  });

  it('requires assumption handling mode to match the review disposition', () => {
    const invalidFixture = structuredClone(fixtures.review) as {
      reviews: Array<Record<string, unknown>>;
    };
    invalidFixture.reviews[1].claimId = 'SEC-CLAIM-003';
    invalidFixture.reviews[1].claimType = 'assumption';
    invalidFixture.reviews[1].assumptionHandling = {
      mode: 'assumption-validation-required',
      rationale: 'Out-of-scope assumption findings should remain residual-risk evidence.',
      evidenceRefs: ['SEC-CLAIM-003', 'SEC-FINDING-002'],
    };

    expect(validateSecurityReviewSemantics(invalidFixture)).toEqual([
      expect.objectContaining({
        keyword: 'assumption_handling_mode_mismatch',
        instancePath: '/reviews/1/assumptionHandling/mode',
      }),
    ]);
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


  it('keeps boundary security review fixtures schema-valid', () => {
    const validate = buildValidator(schemas.review);

    expect(validate(boundaryFixtures.multipleReviewRecords), JSON.stringify(validate.errors)).toBe(true);
    expect(validateSecurityReviewSemantics(boundaryFixtures.multipleReviewRecords)).toHaveLength(0);
    expect(validate(boundaryFixtures.trustBoundaryUnknown), JSON.stringify(validate.errors)).toBe(true);
    expect(validateSecurityReviewSemantics(boundaryFixtures.trustBoundaryUnknown)).toHaveLength(0);
  });

  it('allows multiple review records for a single candidate finding', () => {
    const reviews = boundaryFixtures.multipleReviewRecords.reviews as Array<{ findingId: string; result: string }>;

    expect(reviews.filter((review) => review.findingId === 'SEC-FINDING-001')).toHaveLength(2);
    expect(reviews.map((review) => review.result)).toEqual(['needs-human-review', 'confirmed']);
  });

  it('preserves trust-boundary unknown as a candidate-first review scenario', () => {
    const reviews = boundaryFixtures.trustBoundaryUnknown.reviews as Array<{
      result: string;
      gates: { trustBoundary: { result: string } };
    }>;

    expect(reviews[0]?.result).toBe('needs-human-review');
    expect(reviews[0]?.gates.trustBoundary.result).toBe('unknown');
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
