import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/assurance/aggregate-lanes.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

const writeJson = (targetPath: string, payload: unknown) => {
  writeFileSync(targetPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
};

const createVerifyLiteSummary = (overrides = {}) => ({
  schemaVersion: '1.0.0',
  timestamp: '2026-03-08T09:00:00.000Z',
  metadata: {
    generatedAtUtc: '2026-03-08T09:00:00.000Z',
    generatedAtLocal: '2026-03-08T18:00:00.000+09:00',
    timezoneOffset: '+09:00',
    gitCommit: '0123456789abcdef0123456789abcdef01234567',
    branch: 'main',
    runner: {
      name: 'local',
      os: 'linux',
      arch: 'x64',
      ci: false,
    },
    toolVersions: {
      node: 'v22.0.0',
    },
  },
  flags: {
    install: '',
    noFrozen: false,
    keepLintLog: false,
    enforceLint: false,
    runMutation: true,
  },
  steps: {
    install: { status: 'success', notes: null, retried: false },
    contextPackValidation: { status: 'success', notes: null },
    contextPackProductCoproductValidation: { status: 'success', notes: null },
    conformanceReport: { status: 'success', notes: null },
  },
  artifacts: {
    lintSummary: null,
    lintLog: null,
    mutationSummary: 'artifacts/testing/mutation-summary.json',
    mutationSurvivors: 'artifacts/testing/mutation-survivors.json',
    contextPackReportJson: 'artifacts/context-pack/context-pack-validate-report.json',
    contextPackReportMarkdown: null,
    contextPackFunctorReportJson: null,
    contextPackFunctorReportMarkdown: null,
    contextPackNaturalTransformationReportJson: null,
    contextPackNaturalTransformationReportMarkdown: null,
    contextPackProductCoproductReportJson: 'artifacts/context-pack/context-pack-product-coproduct-report.json',
    contextPackProductCoproductReportMarkdown: null,
    contextPackPhase5ReportJson: null,
    contextPackPhase5ReportMarkdown: null,
    conformanceSummary: 'artifacts/hermetic-reports/conformance/summary.json',
    conformanceSummaryMarkdown: null,
  },
  ...overrides,
});

const createFormalSummary = () => ({
  schemaVersion: 'formal-summary/v2',
  contractId: 'formal-summary.v2',
  tool: 'aggregate',
  status: 'ok',
  ok: true,
  generatedAtUtc: '2026-03-08T09:05:00.000Z',
  metadata: {
    generatedAtUtc: '2026-03-08T09:05:00.000Z',
    generatedAtLocal: '2026-03-08T18:05:00.000+09:00',
    timezoneOffset: '+09:00',
    gitCommit: '0123456789abcdef0123456789abcdef01234567',
    branch: 'main',
    runner: {
      name: 'local',
      os: 'linux',
      arch: 'x64',
      ci: false,
    },
    toolVersions: {
      node: 'v22.0.0',
    },
  },
  results: [
    {
      name: 'conformance',
      status: 'ok',
      code: 0,
      durationMs: 15,
      logPath: 'artifacts/hermetic-reports/conformance/summary.json',
      reason: null,
    },
    {
      name: 'lean',
      status: 'ok',
      code: 0,
      durationMs: 7,
      logPath: 'artifacts/formal/lean-output.txt',
      reason: null,
    },
  ],
});

const createConformanceReport = () => ({
  schemaVersion: '1.0.0',
  generatedAt: '2026-03-08T09:06:00.000Z',
  status: 'success',
  runsAnalyzed: 2,
  statusBreakdown: { pass: 2, fail: 0, skip: 0, error: 0, timeout: 0 },
  totals: {
    rulesExecuted: 4,
    rulesPassed: 4,
    rulesFailed: 0,
    rulesErrored: 0,
    rulesSkipped: 0,
    totalViolations: 0,
    uniqueRules: 4,
    uniqueViolationRules: 0,
  },
  severityTotals: { critical: 0, major: 0, minor: 0, info: 0, warning: 0 },
  categoryTotals: {
    data_validation: 0,
    api_contract: 0,
    business_logic: 0,
    security_policy: 0,
    performance_constraint: 0,
    resource_usage: 0,
    state_invariant: 0,
    behavioral_constraint: 0,
    integration_requirement: 0,
    compliance_rule: 0,
  },
  severityTrends: [],
  topViolations: [],
  inputs: [],
});

const createCounterexample = (overrides = {}) => ({
  schemaVersion: '1.0.0',
  backend: 'tlc',
  spec: 'spec/tla/Inventory.tla',
  claimIds: ['no-negative-stock'],
  morphismIds: ['ReserveInventory'],
  triageStatus: 'resolved',
  replayCommand: 'pnpm run model-check -- --spec spec/tla/Inventory.tla',
  suggestedContextChanges: {
    summary: 'Strengthen reservation precondition.',
    contextPackSuggestionPath: 'artifacts/context-pack/context-pack-suggestions.json',
  },
  violated: {
    kind: 'INVARIANT',
    name: 'NoNegativeStock',
    message: 'stock dropped below zero',
  },
  trace: [
    {
      index: 0,
      state: {
        stock: 0,
      },
    },
  ],
  ...overrides,
});

const createEvidenceManifest = (entries: Array<Record<string, unknown>>) => ({
  schemaVersion: 'assurance-evidence-manifest/v1',
  entries,
});

const runScript = (args: string[], cwd = repoRoot) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd,
    encoding: 'utf8',
    timeout: 120_000,
    env: {
      ...process.env,
      NODE_OPTIONS: '',
    },
  });

describe.sequential('assurance aggregate lanes script', () => {
  it('parses arguments and aggregates observed lanes with supplemental evidence', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs(['--assurance-profile', 'fixtures/assurance/sample.assurance-profile.json'])).toMatchObject({
      assuranceProfile: 'fixtures/assurance/sample.assurance-profile.json',
      securityClaims: null,
      securityFindings: null,
      securityReview: null,
      outputJson: 'artifacts/assurance/assurance-summary.json',
      outputMd: 'artifacts/assurance/assurance-summary.md',
    });
    expect(() => mod.parseArgs(['--assurance-profile'])).toThrow('--assurance-profile requires a value');

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-aggregate-success-'));
    const verifyLitePath = join(sandbox, 'verify-lite-run-summary.json');
    const formalSummaryPath = join(sandbox, 'formal-summary-v2.json');
    const conformanceReportPath = join(sandbox, 'conformance-report.json');
    const counterexamplePath = join(sandbox, 'counterexample.json');
    const evidenceManifestPath = join(sandbox, 'evidence-manifest.json');
    const outputJson = join(sandbox, 'assurance-summary.json');
    const outputMd = join(sandbox, 'assurance-summary.md');

    try {
      writeJson(verifyLitePath, createVerifyLiteSummary());
      writeJson(formalSummaryPath, createFormalSummary());
      writeJson(conformanceReportPath, createConformanceReport());
      writeJson(counterexamplePath, createCounterexample());
      writeJson(
        evidenceManifestPath,
        createEvidenceManifest([
          {
            lane: 'behavior',
            kind: 'property',
            sourceKind: 'source-derived',
            claimIds: ['no-negative-stock'],
            artifactPath: 'artifacts/testing/property-summary.json',
            generatorLineage: 'property-harness',
            detail: 'property suite passed',
          },
          {
            lane: 'runtime',
            kind: 'runtime-alert',
            sourceKind: 'runtime-derived',
            claimIds: ['no-negative-stock'],
            artifactPath: 'artifacts/runtime/alerts/no-negative-stock.json',
            generatorLineage: 'runtime-guard',
            detail: 'runtime alert configured',
          },
        ]),
      );

      const result = runScript([
        '--assurance-profile',
        'fixtures/assurance/sample.assurance-profile.json',
        '--context-pack',
        'fixtures/context-pack/sample.context-pack.json',
        '--verify-lite-summary',
        verifyLitePath,
        '--formal-summary',
        formalSummaryPath,
        '--conformance-report',
        conformanceReportPath,
        '--counterexample',
        counterexamplePath,
        '--evidence-manifest',
        evidenceManifestPath,
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('[assurance] wrote summary');

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.schemaVersion).toBe('assurance-summary/v1');
      expect(summary.summary.claimCount).toBe(1);
      expect(summary.summary.warningCount).toBe(0);
      expect(summary.claims[0]).toMatchObject({
        claimId: 'no-negative-stock',
        status: 'satisfied',
        observedLanes: ['spec', 'behavior', 'adversarial', 'model', 'proof', 'runtime'],
        missingLanes: [],
        observedEvidenceKinds: expect.arrayContaining(['property', 'product-coproduct', 'counterexample-closed']),
      });
      expect(summary.claims[0].counterexamples).toMatchObject({
        open: 0,
        resolved: 1,
        acceptedRisk: 0,
        total: 1,
      });
      expect(summary.laneCoverage.proof.observedClaims).toBe(1);
      expect(readFileSync(outputMd, 'utf8')).toContain('## Claim status');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('adds security claim and review evidence to the assurance lane summary', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-aggregate-security-'));
    const securityReviewPath = join(sandbox, 'security-review-with-repeat.json');
    const outputJson = join(sandbox, 'assurance-summary.json');
    const outputMd = join(sandbox, 'assurance-summary.md');

    try {
      const securityReviewFixture = JSON.parse(
        readFileSync(resolve(repoRoot, 'fixtures/security-assurance/sample.security-review.json'), 'utf8'),
      );
      securityReviewFixture.reviews.push({
        ...securityReviewFixture.reviews[0],
        reviewer: 'human-security-reviewer',
        reviewerNotes: ['Human reviewer rechecked the same finding and kept the review state.'],
      });
      writeJson(securityReviewPath, securityReviewFixture);

      const result = runScript([
        '--assurance-profile',
        'fixtures/assurance/sample.assurance-profile.json',
        '--security-claims',
        'fixtures/security-assurance/sample.security-claims.json',
        '--security-findings',
        'fixtures/security-assurance/sample.security-findings.json',
        '--security-review',
        securityReviewPath,
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.inputs.securityClaims).toContain('fixtures/security-assurance/sample.security-claims.json');
      expect(summary.inputs.securityFindings).toContain('fixtures/security-assurance/sample.security-findings.json');
      expect(summary.inputs.securityReview).toContain(securityReviewPath);
      expect(summary.summary.claimCount).toBe(2);

      const securityClaim = summary.claims.find((claim: { claimId: string }) => claim.claimId === 'SEC-CLAIM-001');
      expect(securityClaim).toMatchObject({
        criticality: 'high',
        securityClaimType: 'invariant',
        observedLanes: ['spec', 'adversarial'],
        missingLanes: ['behavior'],
      });
      expect(securityClaim.observedEvidenceKinds).toEqual(
        expect.arrayContaining(['security-claim', 'security-finding', 'security-review']),
      );
      expect(
        securityClaim.evidence.filter((entry: { kind: string }) => entry.kind === 'security-review'),
      ).toHaveLength(4);
      expect(securityClaim.counterexamples).toMatchObject({
        open: 1,
        resolved: 2,
        total: 3,
      });
      expect(securityClaim.independenceWarnings).toContain('unresolved-critical-counterexample');
      expect(readFileSync(outputMd, 'utf8')).toContain('SEC-CLAIM-001');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('builds a reviewer decision surface from producer, boundary, claim, waiver, and policy summaries', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-review-surface-'));
    const claimEvidenceManifestPath = join(sandbox, 'claim-evidence-manifest.json');
    const policyDecisionPath = join(sandbox, 'policy-decision.json');
    const outputJson = join(sandbox, 'assurance-summary.json');
    const outputMd = join(sandbox, 'assurance-summary.md');

    try {
      const claimEvidenceManifest = JSON.parse(
        readFileSync(resolve(repoRoot, 'fixtures/assurance/sample.claim-evidence-manifest.json'), 'utf8'),
      );
      claimEvidenceManifest.claims.push({
        id: 'unresolved-without-missing',
        statement: 'Reviewer must still see unresolved claims that do not carry missingEvidenceRefs.',
        criticality: 'medium',
        targetLevel: 'A2',
        achievedLevel: 'A1',
        status: 'unresolved',
        evidenceRefs: [],
        proofObligationRefs: [],
        missingEvidenceRefs: [],
        waiverRefs: [],
        notes: ['Regression fixture for Markdown unresolved claim visibility.'],
      });
      writeJson(claimEvidenceManifestPath, claimEvidenceManifest);

      const policyDecision = JSON.parse(
        readFileSync(resolve(repoRoot, 'fixtures/policy/sample.policy-decision-v1.json'), 'utf8'),
      );
      policyDecision.evaluation.assurance.summary.activeWaivers = 1;
      policyDecision.evaluation.assurance.summary.expiringSoonWaivers = 1;
      policyDecision.evaluation.assurance.waivers[0].status = 'expiringSoon';
      writeJson(policyDecisionPath, policyDecision);

      const result = runScript([
        '--assurance-profile',
        'fixtures/assurance/sample.assurance-profile.json',
        '--context-pack',
        'fixtures/context-pack/sample.context-pack.json',
        '--producer-summary',
        'fixtures/agents/producer-normalization-summary.codex.json',
        '--boundary-map-summary',
        'fixtures/context-pack/sample.boundary-map-summary.json',
        '--claim-evidence-manifest',
        claimEvidenceManifestPath,
        '--policy-decision',
        policyDecisionPath,
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.inputs).toMatchObject({
        producerSummaries: [resolve(repoRoot, 'fixtures/agents/producer-normalization-summary.codex.json')],
        boundaryMapSummaries: [resolve(repoRoot, 'fixtures/context-pack/sample.boundary-map-summary.json')],
        claimEvidenceManifests: [claimEvidenceManifestPath],
        policyDecision: policyDecisionPath,
      });
      expect(summary.reviewSurface).toMatchObject({
        schemaVersion: 'assurance-review-surface/v1',
        recommendedReviewerAction: {
          action: 'review-boundary-map',
        },
        producerSignals: {
          status: 'report-only-findings',
          missingEvidence: 1,
          reportOnlyFindings: 3,
          controlPlaneJudgment: {
            emittedDecisionCount: 0,
            expected: 'producer-output-is-not-control-plane-judgment',
          },
        },
        boundaryMap: {
          status: 'drift',
          evidenceKind: 'design-boundary',
          totalFindings: 1,
        },
        claimEvidence: {
          manifestStatusCounts: {
            satisfied: 1,
            partial: 2,
            waived: 1,
            unresolved: 1,
          },
        },
        waivers: {
          active: 1,
          expiringSoon: 1,
          claims: ['manual-fraud-review'],
          waiverRefs: [
            expect.objectContaining({
              id: 'waiver-manual-fraud-review-001',
              status: 'expiringSoon',
              source: 'claim-evidence-manifest, policy-decision',
            }),
          ],
        },
        policyDecision: {
          status: 'present',
          mode: 'report-only',
          result: 'waived',
          enforced: false,
        },
      });
      expect(summary.reviewSurface.claimEvidence.missingEvidenceClaims).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            claimId: 'no-negative-balance',
            status: 'partial',
          }),
          expect.objectContaining({
            claimId: 'manual-fraud-review',
            status: 'waived',
          }),
        ]),
      );
      expect(summary.reviewSurface.interpretationNotes).toEqual(
        expect.arrayContaining([
          'Producer assertions remain producer assertions; control-plane judgment must come from reviewed, schema-backed evidence and policy artifacts.',
          'tested and proved are distinct evidence outcomes; runtime-mitigated is not proof.',
          'waived is an explicit exception state and must not be counted as satisfied.',
        ]),
      );
      expect(summary.reviewSurface.residualRisks).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ kind: 'producer-report-only-finding' }),
          expect.objectContaining({ kind: 'boundary-map-evidence-gap' }),
          expect.objectContaining({ kind: 'missing-evidence', claimId: 'no-negative-balance' }),
          expect.objectContaining({ kind: 'waiver-review-required' }),
        ]),
      );

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('## Reviewer decision surface');
      expect(markdown).toContain('producerSignals: report-only-findings');
      expect(markdown).toContain('boundaryMap: drift');
      expect(markdown).toContain('### Unresolved claims');
      expect(markdown).toContain('unresolved-without-missing');
      expect(markdown).toContain('tested and proved are distinct evidence outcomes');
      expect(markdown).toContain('runtime-mitigated is not proof');
      expect(markdown).toContain('waived is an explicit exception state');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('recommends waiver review when only expiring-soon waiver risk remains', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-review-expiring-waiver-'));
    const assuranceProfilePath = join(sandbox, 'assurance-profile.json');
    const contextPackPath = join(sandbox, 'context-pack.json');
    const claimEvidenceManifestPath = join(sandbox, 'claim-evidence-manifest.json');
    const policyDecisionPath = join(sandbox, 'policy-decision.json');
    const outputJson = join(sandbox, 'assurance-summary.json');

    try {
      writeJson(assuranceProfilePath, {
        schemaVersion: 'assurance-profile/v1',
        profileId: 'expiring-waiver-profile',
        claims: [
          {
            id: 'waiver-sensitive-claim',
            statement: 'Waiver-sensitive claim remains visible for review.',
            criticality: 'medium',
            targetLevel: 'A1',
            minIndependentSources: 1,
            requiredLanes: ['spec'],
            requiredEvidenceKinds: ['schema'],
          },
        ],
      });
      writeJson(contextPackPath, {
        schemaVersion: 'context-pack/v1',
        assurance: {
          profile: 'expiring-waiver-profile',
          claim_refs: ['waiver-sensitive-claim'],
        },
      });
      writeJson(claimEvidenceManifestPath, {
        schemaVersion: 'claim-evidence-manifest/v1',
        generatedAt: '2026-06-20T00:00:00.000Z',
        sourceArtifacts: [],
        claims: [
          {
            id: 'waiver-sensitive-claim',
            statement: 'Waiver-sensitive claim remains visible for review.',
            criticality: 'medium',
            targetLevel: 'A1',
            achievedLevel: 'A1',
            status: 'waived',
            evidenceRefs: [],
            proofObligationRefs: [],
            missingEvidenceRefs: [],
            waiverRefs: [
              {
                id: 'waiver-expiring-001',
                status: 'active',
                owner: '@team-risk',
                expires: '2026-06-30',
                reason: 'Temporary exception is active but expiring soon.',
              },
            ],
            notes: [],
          },
        ],
      });
      writeJson(policyDecisionPath, {
        schemaVersion: '1.0.0',
        evaluation: {
          ok: true,
          assurance: {
            mode: 'report-only',
            result: 'waived',
            summary: {
              totalClaims: 1,
              pass: 0,
              waived: 1,
              reportOnly: 0,
              block: 0,
              activeWaivers: 0,
              expiringSoonWaivers: 1,
              expiredWaivers: 0,
              orphanWaivers: 0,
            },
            claims: [],
            waivers: [
              {
                id: 'waiver-expiring-001',
                claimId: 'waiver-sensitive-claim',
                status: 'expiringSoon',
                owner: '@team-risk',
                expires: '2026-06-30',
                reason: 'Temporary exception is active but expiring soon.',
              },
            ],
          },
        },
      });

      const result = runScript([
        '--assurance-profile',
        assuranceProfilePath,
        '--context-pack',
        contextPackPath,
        '--claim-evidence-manifest',
        claimEvidenceManifestPath,
        '--policy-decision',
        policyDecisionPath,
        '--output-json',
        outputJson,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.reviewSurface).toMatchObject({
        recommendedReviewerAction: {
          action: 'review-waivers',
        },
        waivers: {
          active: 0,
          expiringSoon: 1,
          expired: 0,
          orphan: 0,
          waiverRefs: [
            expect.objectContaining({
              id: 'waiver-expiring-001',
              status: 'expiringSoon',
            }),
          ],
        },
      });
      expect(summary.reviewSurface.residualRisks).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            kind: 'waiver-review-required',
            reason: expect.stringContaining('expiringSoon=1'),
          }),
        ]),
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('treats assumption validation requirements as claim warnings', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-aggregate-assumption-warning-'));
    const assuranceProfilePath = join(sandbox, 'assurance-profile.json');
    const securityClaimsPath = join(sandbox, 'security-claims.json');
    const securityFindingsPath = join(sandbox, 'security-findings.json');
    const securityReviewPath = join(sandbox, 'security-review.json');
    const outputJson = join(sandbox, 'assurance-summary.json');

    try {
      writeJson(assuranceProfilePath, {
        schemaVersion: 'assurance-profile/v1',
        profileId: 'assumption-warning-profile',
        claims: [
          {
            id: 'SEC-CLAIM-ASSUMPTION',
            statement: 'Deployment topology assumption must be validated before vulnerability interpretation.',
            criticality: 'low',
            targetLevel: 'A1',
            minIndependentSources: 1,
            requiredLanes: ['spec', 'adversarial'],
            requiredEvidenceKinds: [],
          },
        ],
      });
      writeJson(securityClaimsPath, {
        schemaVersion: 'security-claim/v1',
        claims: [
          {
            id: 'SEC-CLAIM-ASSUMPTION',
            type: 'assumption',
            statement: 'Deployment topology assumption must be validated before vulnerability interpretation.',
            criticality: 'low',
            targetLevel: 'A1',
            minIndependentSources: 1,
            requiredLanes: ['spec', 'adversarial'],
          },
        ],
      });
      writeJson(securityFindingsPath, {
        schemaVersion: 'security-finding/v1',
        findings: [
          {
            id: 'SEC-FINDING-ASSUMPTION',
            claimId: 'SEC-CLAIM-ASSUMPTION',
            status: 'candidate',
            severity: 'low',
            title: 'Assumption validation required',
            summary: 'The finding depends on an unvalidated deployment assumption.',
            affectedLocations: [],
            provenance: { origin: 'fixture', generator: 'assumption-warning-test' },
          },
        ],
      });
      writeJson(securityReviewPath, {
        schemaVersion: 'security-review/v1',
        reviews: [
          {
            findingId: 'SEC-FINDING-ASSUMPTION',
            claimId: 'SEC-CLAIM-ASSUMPTION',
            claimType: 'assumption',
            severity: 'low',
            result: 'needs-human-review',
            gates: {
              deadCode: { result: 'pass', rationale: 'Reachability is plausible.' },
              trustBoundary: { result: 'pass', rationale: 'Trust boundary depends on deployment topology.' },
              scope: { result: 'pass', rationale: 'Finding is in scope pending assumption validation.' },
            },
            falsePositiveRootCause: null,
            assumptionHandling: {
              mode: 'assumption-validation-required',
              rationale: 'Validate deployment topology before classifying this as a direct vulnerability.',
              evidenceRefs: ['SEC-CLAIM-ASSUMPTION', 'SEC-FINDING-ASSUMPTION'],
            },
            reviewerNotes: ['Assumption validation is still required.'],
            reviewer: 'assumption-warning-test',
          },
        ],
      });

      const result = runScript([
        '--assurance-profile',
        assuranceProfilePath,
        '--security-claims',
        securityClaimsPath,
        '--security-findings',
        securityFindingsPath,
        '--security-review',
        securityReviewPath,
        '--output-json',
        outputJson,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.summary).toMatchObject({
        satisfiedClaims: 0,
        warningClaims: 1,
      });
      expect(summary.claims[0]).toMatchObject({
        claimId: 'SEC-CLAIM-ASSUMPTION',
        status: 'warning',
        securityClaimType: 'assumption',
        independenceWarnings: expect.arrayContaining(['assumption-validation-required']),
      });
      expect(summary.warnings).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            claimId: 'SEC-CLAIM-ASSUMPTION',
            code: 'assumption-validation-required',
          }),
        ]),
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('reports missing spec-derived evidence and unresolved critical counterexamples', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-aggregate-warning-'));
    const counterexamplePath = join(sandbox, 'counterexample.json');
    const evidenceManifestPath = join(sandbox, 'evidence-manifest.json');
    const outputJson = join(sandbox, 'assurance-summary.json');

    try {
      writeJson(
        counterexamplePath,
        createCounterexample({
          backend: 'property',
          triageStatus: 'open',
        }),
      );
      writeJson(
        evidenceManifestPath,
        createEvidenceManifest([
          {
            lane: 'behavior',
            kind: 'property',
            sourceKind: 'source-derived',
            claimIds: ['no-negative-stock'],
            artifactPath: 'artifacts/testing/property-summary.json',
            generatorLineage: 'property-harness',
          },
        ]),
      );

      const result = runScript([
        '--assurance-profile',
        'fixtures/assurance/sample.assurance-profile.json',
        '--counterexample',
        counterexamplePath,
        '--evidence-manifest',
        evidenceManifestPath,
        '--output-json',
        outputJson,
      ]);
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.summary.warningCount).toBeGreaterThan(0);
      expect(summary.claims[0].status).toBe('warning');
      expect(summary.claims[0].independenceWarnings).toEqual(
        expect.arrayContaining([
          'missing-spec-derived-evidence',
          'unresolved-critical-counterexample',
          'insufficient-independent-lanes',
        ]),
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('fails fast when the assurance profile contains duplicate claim ids', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-assurance-aggregate-duplicate-claims-'));
    const assuranceProfilePath = join(sandbox, 'assurance-profile.json');

    try {
      writeJson(assuranceProfilePath, {
        schemaVersion: 'assurance-profile/v1',
        profileId: 'duplicate-claims-v1',
        scope: {
          contextPackSources: ['spec/context-pack/**/*.json'],
          componentGlobs: ['src/**'],
        },
        claims: [
          {
            id: 'duplicate-claim',
            statement: 'First claim.',
            kind: 'safety',
            criticality: 'medium',
            targetLevel: 'A1',
            requiredLanes: ['spec'],
            requiredEvidenceKinds: ['schema'],
          },
          {
            id: 'duplicate-claim',
            statement: 'Second claim.',
            kind: 'safety',
            criticality: 'medium',
            targetLevel: 'A1',
            requiredLanes: ['behavior'],
            requiredEvidenceKinds: ['property'],
          },
        ],
      });

      const result = runScript([
        '--assurance-profile',
        assuranceProfilePath,
      ]);
      expect(result.status).toBe(1);
      expect(result.stderr).toContain('duplicate claim ids');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
