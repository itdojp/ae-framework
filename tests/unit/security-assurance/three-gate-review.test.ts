import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { generateSecurityThreeGateReview } from '../../../src/security/assurance/three-gate-review.js';

const findingsPath = 'fixtures/security-assurance/sample.security-findings.json';
const scopePath = 'fixtures/security-assurance/sample.security-audit-scope.json';
const codeMapPath = 'fixtures/security-assurance/sample.security-code-map.json';
const entrypointMapPath = 'fixtures/security-assurance/sample.security-entrypoint-map.json';
const generatedAt = '2026-05-07T00:00:00.000Z';
const tsxBin = resolve('node_modules/.bin/tsx');

const readJson = <T>(path: string): T => JSON.parse(readFileSync(path, 'utf8')) as T;

const writeJson = (filePath: string, value: unknown) => {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

const entrypointMapFixture = ({
  id = 'EP-001',
  attackerControlled = true,
  reachPath = 'src/cache.ts',
  trustBoundaryIds = ['TB-001'],
}: {
  id?: string;
  attackerControlled?: boolean;
  reachPath?: string;
  trustBoundaryIds?: string[];
} = {}) => ({
  schemaVersion: 'security-entrypoint-map/v1',
  generatedAt,
  entrypoints: [
    {
      id,
      kind: 'api-route',
      name: 'POST /verify',
      path: 'src/routes/verify.ts',
      startLine: 1,
      endLine: 30,
      trustBoundaryIds,
      attackerControlled,
      reaches: [
        {
          path: reachPath,
          startLine: 7,
          endLine: 15,
          symbol: 'buildCacheKey',
          reason: 'Fixture entrypoint reaches the cache key builder.',
        },
      ],
    },
  ],
  summary: {
    totalEntrypoints: 1,
    attackerControlledEntrypoints: attackerControlled ? 1 : 0,
    totalReachableLocations: 1,
    byKind: { 'api-route': 1 },
  },
  provenance: {
    origin: 'fixture',
    generator: 'three-gate-review-test',
    source: 'entrypoint-map.json',
  },
});

describe('security three-gate review producer', () => {
  it('classifies candidate findings through scope, dead-code, and trust-boundary gates', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-'));
    try {
      const result = await generateSecurityThreeGateReview(findingsPath, scopePath, codeMapPath, outDir, { generatedAt });

      expect(result.review).toEqual(
        expect.objectContaining({
          schemaVersion: 'security-review/v1',
          generatedAt,
          summary: expect.objectContaining({
            totalReviews: 3,
            byResult: expect.objectContaining({ needsHumanReview: 1, rejected: 1, outOfScope: 1 }),
            falsePositiveRootCauses: expect.objectContaining({ deadCode: 1, outOfScope: 1 }),
          }),
        }),
      );

      const reviewsByFinding = new Map(result.review.reviews.map((review) => [review.findingId, review]));
      expect(reviewsByFinding.get('SEC-FINDING-001')).toEqual(
        expect.objectContaining({
          severity: 'high',
          result: 'needs-human-review',
          falsePositiveRootCause: null,
          gates: expect.objectContaining({
            deadCode: expect.objectContaining({ result: 'pass' }),
            trustBoundary: expect.objectContaining({ result: 'pass' }),
            scope: expect.objectContaining({ result: 'pass' }),
          }),
        }),
      );
      expect(reviewsByFinding.get('SEC-FINDING-002')).toEqual(
        expect.objectContaining({
          severity: 'medium',
          result: 'out-of-scope',
          falsePositiveRootCause: 'out-of-scope',
          gates: expect.objectContaining({ scope: expect.objectContaining({ result: 'fail' }) }),
        }),
      );
      expect(reviewsByFinding.get('SEC-FINDING-003')).toEqual(
        expect.objectContaining({
          severity: 'low',
          result: 'rejected',
          falsePositiveRootCause: 'dead-code',
          gates: expect.objectContaining({
            deadCode: expect.objectContaining({ result: 'fail' }),
            trustBoundary: expect.objectContaining({ result: 'unknown' }),
            scope: expect.objectContaining({ result: 'pass' }),
          }),
        }),
      );

      expect(readJson<{ reviews: unknown[] }>(join(outDir, 'security-review.json')).reviews).toHaveLength(3);
      expect(readFileSync(join(outDir, 'security-review.md'), 'utf8')).toContain('Security three-gate review summary');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('uses optional entrypoint-map evidence for the trust-boundary gate', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-entrypoint-'));
    try {
      const result = await generateSecurityThreeGateReview(findingsPath, scopePath, codeMapPath, outDir, {
        generatedAt,
        entrypointMapPath,
      });

      const reviewsByFinding = new Map(result.review.reviews.map((review) => [review.findingId, review]));
      expect(reviewsByFinding.get('SEC-FINDING-001')).toEqual(
        expect.objectContaining({
          result: 'needs-human-review',
          gates: expect.objectContaining({
            trustBoundary: expect.objectContaining({
              result: 'pass',
              rationale: expect.stringContaining('Matched attacker-controlled entrypoint evidence: EP-001'),
              evidenceRefs: expect.arrayContaining(['EP-001', 'TB-001', 'src/cache.ts:7-15']),
            }),
          }),
        }),
      );
      expect(readFileSync(join(outDir, 'security-review.md'), 'utf8')).toContain('Matched attacker-controlled entrypoint evidence: EP-001');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('keeps the trust-boundary gate unknown when entrypoint-map lacks matching reachability evidence', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-review-entrypoint-missing-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-entrypoint-missing-out-'));
    try {
      const localEntrypointMapPath = join(fixtureDir, 'entrypoint-map.json');
      writeJson(localEntrypointMapPath, entrypointMapFixture({ id: 'EP-OTHER', reachPath: 'src/other.ts' }));

      const result = await generateSecurityThreeGateReview(findingsPath, scopePath, codeMapPath, outDir, {
        generatedAt,
        entrypointMapPath: localEntrypointMapPath,
      });

      const review = result.review.reviews.find((entry) => entry.findingId === 'SEC-FINDING-001');
      expect(review).toEqual(
        expect.objectContaining({
          result: 'needs-human-review',
          falsePositiveRootCause: null,
          gates: expect.objectContaining({
            trustBoundary: expect.objectContaining({
              result: 'unknown',
              rationale: 'No entrypoint-map reachability evidence matched affected locations and audit scope trust boundaries.',
            }),
          }),
        }),
      );
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('rejects trust-boundary misunderstanding when only non-attacker-controlled entrypoints reach the location', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-review-entrypoint-internal-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-entrypoint-internal-out-'));
    try {
      const localEntrypointMapPath = join(fixtureDir, 'entrypoint-map.json');
      writeJson(localEntrypointMapPath, entrypointMapFixture({ id: 'EP-INTERNAL', attackerControlled: false }));

      const result = await generateSecurityThreeGateReview(findingsPath, scopePath, codeMapPath, outDir, {
        generatedAt,
        entrypointMapPath: localEntrypointMapPath,
      });

      const review = result.review.reviews.find((entry) => entry.findingId === 'SEC-FINDING-001');
      expect(review).toEqual(
        expect.objectContaining({
          result: 'rejected',
          falsePositiveRootCause: 'trust-boundary-misunderstanding',
          gates: expect.objectContaining({
            trustBoundary: expect.objectContaining({
              result: 'fail',
              rationale: 'Matching entrypoint evidence is not attacker-controlled: EP-INTERNAL.',
              evidenceRefs: expect.arrayContaining(['EP-INTERNAL', 'TB-001', 'src/cache.ts:7-15']),
            }),
          }),
        }),
      );
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('keeps trust-boundary involvement unknown when no explicit boundary evidence is available', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-review-trust-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-trust-out-'));
    try {
      const localFindingsPath = join(fixtureDir, 'findings.json');
      const localScopePath = join(fixtureDir, 'scope.json');
      const localCodeMapPath = join(fixtureDir, 'code-map.json');
      writeJson(localFindingsPath, {
        schemaVersion: 'security-finding/v1',
        generatedAt,
        findings: [
          {
            id: 'SEC-FINDING-TRUST-UNKNOWN',
            claimId: 'SEC-CLAIM-TRUST-UNKNOWN',
            status: 'candidate',
            severity: 'high',
            confidence: 'medium',
            title: 'Mapped cache validation candidate',
            summary: 'The finding maps to production code, but does not cite a concrete trust boundary.',
            affectedLocations: [
              { path: 'src/cache.ts', startLine: 10, endLine: 20, symbol: 'validateCache', description: 'Mapped production code.' },
            ],
            proofAttempt: {
              claim: 'SEC-CLAIM-TRUST-UNKNOWN',
              map: 'Relevant code path is src/cache.ts.',
              prove: 'The implementation must preserve the security claim.',
              stressTest: 'Boundary evidence is intentionally absent in this fixture.',
              report: 'Keep as a candidate.',
            },
            scopeRefs: ['NON-MATCHING-BOUNDARY'],
            evidenceRefs: [],
            provenance: { origin: 'fixture', generator: 'three-gate-review-test' },
          },
        ],
        summary: {
          totalFindings: 1,
          byStatus: { candidate: 1, needsHumanReview: 0, confirmed: 0, rejected: 0, waived: 0, outOfScope: 0 },
          bySeverity: { low: 0, medium: 0, high: 1, critical: 0 },
        },
      });
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.ts'],
        outOfScope: [],
        trustBoundaries: [
          { id: 'TB-001', name: 'External API', entryPoints: ['api'], attackerControlled: true, scopeRefs: ['src/**/*.ts'] },
        ],
      });
      writeJson(localCodeMapPath, {
        schemaVersion: 'security-code-map/v1',
        generatedAt,
        mappings: [
          {
            claimId: 'SEC-CLAIM-TRUST-UNKNOWN',
            candidateLocations: [{ path: 'src/cache.ts', startLine: 10, endLine: 20, symbol: 'validateCache', reason: 'Mapped by fixture.' }],
            coverage: 'partial',
            warnings: [],
          },
        ],
        summary: { totalClaims: 1, mappedClaims: 1, totalCandidateLocations: 1, totalWarnings: 0, byCoverage: { none: 0, partial: 1, full: 0 } },
        provenance: { origin: 'fixture', generator: 'three-gate-review-test', claims: 'claims.json', scope: 'scope.json', target: 'target' },
        warnings: [],
      });

      const result = await generateSecurityThreeGateReview(localFindingsPath, localScopePath, localCodeMapPath, outDir, { generatedAt });
      expect(result.review.reviews[0]).toEqual(
        expect.objectContaining({
          result: 'needs-human-review',
          falsePositiveRootCause: null,
          gates: expect.objectContaining({
            deadCode: expect.objectContaining({ result: 'pass' }),
            scope: expect.objectContaining({ result: 'pass' }),
            trustBoundary: expect.objectContaining({ result: 'unknown' }),
          }),
        }),
      );
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('uses glob-compatible scope matching for brace patterns', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-review-glob-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-glob-out-'));
    try {
      const localFindingsPath = join(fixtureDir, 'findings.json');
      const localScopePath = join(fixtureDir, 'scope.json');
      const localCodeMapPath = join(fixtureDir, 'code-map.json');
      writeJson(localFindingsPath, {
        schemaVersion: 'security-finding/v1',
        generatedAt,
        findings: [
          {
            id: 'SEC-FINDING-GLOB',
            claimId: 'SEC-CLAIM-GLOB',
            status: 'candidate',
            severity: 'medium',
            confidence: 'medium',
            title: 'Brace glob fixture candidate',
            summary: 'The finding should remain in scope when the scope uses a brace glob.',
            affectedLocations: [
              { path: 'src/cache.ts', startLine: 7, endLine: 15, symbol: 'buildCacheKey', description: 'Brace glob target.' },
            ],
            proofAttempt: {
              claim: 'SEC-CLAIM-GLOB',
              map: 'Relevant code path is src/cache.ts.',
              prove: 'The implementation must preserve the claim.',
              stressTest: 'Use glob-compatible scope matching.',
              report: 'Keep as a candidate.',
            },
            scopeRefs: ['TB-001'],
            evidenceRefs: [],
            provenance: { origin: 'fixture', generator: 'three-gate-review-test' },
          },
        ],
        summary: {
          totalFindings: 1,
          byStatus: { candidate: 1, needsHumanReview: 0, confirmed: 0, rejected: 0, waived: 0, outOfScope: 0 },
          bySeverity: { low: 0, medium: 1, high: 0, critical: 0 },
        },
      });
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.{ts,tsx}'],
        outOfScope: ['src/**/[.]generated.{ts,tsx}'],
        trustBoundaries: [
          { id: 'TB-001', name: 'External API', entryPoints: ['api'], attackerControlled: true, scopeRefs: ['src/**/*.{ts,tsx}'] },
        ],
      });
      writeJson(localCodeMapPath, {
        schemaVersion: 'security-code-map/v1',
        generatedAt,
        mappings: [
          {
            claimId: 'SEC-CLAIM-GLOB',
            candidateLocations: [{ path: 'src/cache.ts', startLine: 7, endLine: 15, symbol: 'buildCacheKey', reason: 'Mapped by fixture.' }],
            coverage: 'partial',
            warnings: [],
          },
        ],
        summary: { totalClaims: 1, mappedClaims: 1, totalCandidateLocations: 1, totalWarnings: 0, byCoverage: { none: 0, partial: 1, full: 0 } },
        provenance: { origin: 'fixture', generator: 'three-gate-review-test', claims: 'claims.json', scope: 'scope.json', target: 'target' },
        warnings: [],
      });

      const result = await generateSecurityThreeGateReview(localFindingsPath, localScopePath, localCodeMapPath, outDir, { generatedAt });
      expect(result.review.reviews[0]).toEqual(
        expect.objectContaining({
          result: 'needs-human-review',
          gates: expect.objectContaining({
            deadCode: expect.objectContaining({ result: 'pass' }),
            trustBoundary: expect.objectContaining({ result: 'pass' }),
            scope: expect.objectContaining({ result: 'pass', evidenceRefs: ['src/**/*.{ts,tsx}'] }),
          }),
        }),
      );
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('relativizes absolute finding and code-map paths under repoRoot without stripping external roots', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-review-absolute-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-absolute-out-'));
    try {
      const absoluteSourcePath = join(fixtureDir, 'src', 'cache.ts');
      const localFindingsPath = join(fixtureDir, 'findings.json');
      const localScopePath = join(fixtureDir, 'scope.json');
      const localCodeMapPath = join(fixtureDir, 'code-map.json');
      writeJson(localFindingsPath, {
        schemaVersion: 'security-finding/v1',
        generatedAt,
        findings: [
          {
            id: 'SEC-FINDING-ABSOLUTE',
            claimId: 'SEC-CLAIM-ABSOLUTE',
            status: 'candidate',
            severity: 'medium',
            confidence: 'medium',
            title: 'Absolute path fixture candidate',
            summary: 'The finding and code map use absolute paths under repoRoot.',
            affectedLocations: [
              { path: absoluteSourcePath, startLine: 7, endLine: 15, symbol: 'buildCacheKey', description: 'Absolute path target.' },
            ],
            proofAttempt: {
              claim: 'SEC-CLAIM-ABSOLUTE',
              map: 'Relevant code path is absolute but under repoRoot.',
              prove: 'The implementation must preserve the claim.',
              stressTest: 'Use shared path normalization.',
              report: 'Keep as a candidate.',
            },
            scopeRefs: ['TB-001'],
            evidenceRefs: [],
            provenance: { origin: 'fixture', generator: 'three-gate-review-test' },
          },
        ],
        summary: {
          totalFindings: 1,
          byStatus: { candidate: 1, needsHumanReview: 0, confirmed: 0, rejected: 0, waived: 0, outOfScope: 0 },
          bySeverity: { low: 0, medium: 1, high: 0, critical: 0 },
        },
      });
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.ts'],
        outOfScope: [],
        trustBoundaries: [
          { id: 'TB-001', name: 'External API', entryPoints: ['api'], attackerControlled: true, scopeRefs: ['src/**/*.ts'] },
        ],
      });
      writeJson(localCodeMapPath, {
        schemaVersion: 'security-code-map/v1',
        generatedAt,
        mappings: [
          {
            claimId: 'SEC-CLAIM-ABSOLUTE',
            candidateLocations: [{ path: absoluteSourcePath, startLine: 7, endLine: 15, symbol: 'buildCacheKey', reason: 'Mapped by fixture.' }],
            coverage: 'partial',
            warnings: [],
          },
        ],
        summary: { totalClaims: 1, mappedClaims: 1, totalCandidateLocations: 1, totalWarnings: 0, byCoverage: { none: 0, partial: 1, full: 0 } },
        provenance: { origin: 'fixture', generator: 'three-gate-review-test', claims: 'claims.json', scope: 'scope.json', target: 'target' },
        warnings: [],
      });

      const result = await generateSecurityThreeGateReview(localFindingsPath, localScopePath, localCodeMapPath, outDir, { generatedAt, repoRoot: fixtureDir });
      expect(result.review.reviews[0]).toEqual(
        expect.objectContaining({
          result: 'needs-human-review',
          gates: expect.objectContaining({
            deadCode: expect.objectContaining({ result: 'pass', evidenceRefs: ['src/cache.ts:7-15'] }),
            trustBoundary: expect.objectContaining({ result: 'pass' }),
            scope: expect.objectContaining({ result: 'pass', evidenceRefs: ['src/**/*.ts'] }),
          }),
        }),
      );
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('exposes the review producer through ae security review', () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-review-cli-'));
    try {
      const result = spawnSync(
        tsxBin,
        [
          'src/cli/index.ts',
          'security',
          'review',
          '--findings',
          findingsPath,
          '--scope',
          scopePath,
          '--code-map',
          codeMapPath,
          '--entrypoint-map',
          entrypointMapPath,
          '--out',
          outDir,
          '--generated-at',
          generatedAt,
        ],
        {
          encoding: 'utf8',
          timeout: 60_000,
          env: {
            ...process.env,
            VITEST: '',
            NODE_ENV: 'production',
            AE_TEST_NO_EXIT: '0',
            DISABLE_TELEMETRY: 'true',
          },
        },
      );

      expect(result.status, `${result.stdout}\n${result.stderr}`).toBe(0);
      expect(result.stdout).toContain('Security three-gate review completed');
      expect(result.stdout).toContain('Reviews: 3');
      const review = readJson<{
        reviews: Array<{ findingId: string; gates: { trustBoundary: { evidenceRefs?: string[] } } }>;
      }>(join(outDir, 'security-review.json'));
      expect(review.reviews).toHaveLength(3);
      expect(review.reviews.find((entry) => entry.findingId === 'SEC-FINDING-001')?.gates.trustBoundary.evidenceRefs).toContain('EP-001');
      expect(readFileSync(join(outDir, 'security-review.md'), 'utf8')).toContain('Dead-code root causes: 1');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });
});
