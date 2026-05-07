import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { generateSecurityProofAudit } from '../../../src/security/assurance/proof-audit.js';

const claimsPath = 'fixtures/security-assurance/sample.security-claims.json';
const codeMapPath = 'fixtures/security-assurance/sample.security-code-map.json';
const scopePath = 'fixtures/security-assurance/sample.security-audit-scope.json';
const responseFixturePath = 'fixtures/security-assurance/sample.security-audit-responses.json';
const generatedAt = '2026-05-07T00:00:00.000Z';
const tsxBin = resolve('node_modules/.bin/tsx');

const readJson = <T>(path: string): T => JSON.parse(readFileSync(path, 'utf8')) as T;

const writeJson = (filePath: string, value: unknown) => {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

describe('security proof-attempt audit producer', () => {
  it('generates a deterministic dry-run audit task bundle without findings', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-proof-audit-dry-'));
    try {
      const result = await generateSecurityProofAudit(claimsPath, codeMapPath, scopePath, outDir, { generatedAt });

      expect(result.taskBundle).toEqual(
        expect.objectContaining({
          schemaVersion: 'security-audit-task-bundle/v1',
          generatedAt,
          summary: expect.objectContaining({
            totalTasks: 1,
            readyTasks: 1,
            blockedTasks: 0,
            totalCandidateLocations: 1,
          }),
        }),
      );
      expect(result.taskBundle.tasks[0]).toEqual(
        expect.objectContaining({
          id: 'SEC-AUDIT-TASK-001',
          claimId: 'SEC-CLAIM-001',
          status: 'ready',
          proofAttemptPrompt: expect.objectContaining({
            map: expect.stringContaining('src/cache.ts:7-15'),
            prove: expect.stringContaining('SEC-CLAIM-001'),
            stressTest: expect.stringContaining('Do not generate exploit automation'),
            report: expect.stringContaining('candidate status'),
          }),
        }),
      );
      expect(result.findings).toBeUndefined();
      expect(result.responseSummary).toEqual({ totalResponses: 0, findingResponses: 0, noFindingResponses: 0, missingResponses: 1 });
      expect(readJson<{ schemaVersion: string }>(join(outDir, 'security-audit-tasks.json')).schemaVersion).toBe('security-audit-task-bundle/v1');
      expect(readFileSync(join(outDir, 'security-audit-summary.md'), 'utf8')).toContain('Dry-run mode');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('normalizes fixture-backed responses into candidate security findings', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-proof-audit-findings-'));
    try {
      const result = await generateSecurityProofAudit(claimsPath, codeMapPath, scopePath, outDir, {
        generatedAt,
        responseFixture: responseFixturePath,
      });

      expect(result.findings?.summary).toEqual(
        expect.objectContaining({
          totalFindings: 2,
          byStatus: expect.objectContaining({ candidate: 2, confirmed: 0 }),
          bySeverity: expect.objectContaining({ high: 1, medium: 1 }),
        }),
      );
      expect(result.findings?.findings.every((finding) => finding['status'] === 'candidate')).toBe(true);
      expect(result.findings?.findings[0]).toEqual(
        expect.objectContaining({
          id: 'SEC-FINDING-001',
          claimId: 'SEC-CLAIM-001',
          proofAttempt: expect.objectContaining({
            claim: 'SEC-CLAIM-001',
            map: expect.any(String),
            prove: expect.any(String),
            stressTest: expect.any(String),
          }),
        }),
      );
      expect(readJson<{ findings: unknown[] }>(join(outDir, 'security-findings.json')).findings).toHaveLength(2);
      expect(readFileSync(join(outDir, 'security-audit-summary.md'), 'utf8')).toContain('Findings generated: 2');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('records no-finding response status in the audit summary while keeping findings candidate-only', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-proof-audit-nofinding-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-proof-audit-nofinding-out-'));
    try {
      mkdirSync(fixtureDir, { recursive: true });
      const localClaimsPath = join(fixtureDir, 'claims.json');
      const localCodeMapPath = join(fixtureDir, 'code-map.json');
      const localScopePath = join(fixtureDir, 'scope.json');
      const localResponsesPath = join(fixtureDir, 'responses.json');
      writeJson(localClaimsPath, {
        schemaVersion: 'security-claim/v1',
        generatedAt,
        claims: [
          {
            id: 'SEC-CLAIM-001',
            type: 'invariant',
            statement: 'Cache key must include attacker-controlled verification fields.',
            sourceRefs: [{ kind: 'spec', uri: 'spec/cache.md' }],
            criticality: 'high',
            targetLevel: 'A2',
            threatTags: { stride: ['Tampering'], cwe: ['CWE-20'] },
            trustBoundary: { boundaryIds: ['TB-001'], entryPoints: ['api'], attackerControlled: true },
            requiredLanes: ['spec'],
            provenance: { origin: 'manual', generator: 'test' },
          },
          {
            id: 'SEC-CLAIM-002',
            type: 'assumption',
            statement: 'Audit scope excludes unrelated fixture helpers.',
            sourceRefs: [{ kind: 'spec', uri: 'spec/cache.md' }],
            criticality: 'medium',
            targetLevel: 'A1',
            threatTags: { stride: ['Tampering'], cwe: ['CWE-20'] },
            trustBoundary: { boundaryIds: ['TB-001'], entryPoints: ['api'], attackerControlled: false },
            requiredLanes: ['spec'],
            provenance: { origin: 'manual', generator: 'test' },
          },
        ],
        summary: { totalClaims: 2, byCriticality: { low: 0, medium: 1, high: 1, critical: 0 } },
      });
      writeJson(localCodeMapPath, {
        schemaVersion: 'security-code-map/v1',
        generatedAt,
        mappings: [
          {
            claimId: 'SEC-CLAIM-001',
            candidateLocations: [{ path: 'src/cache.ts', startLine: 7, endLine: 15, symbol: 'buildCacheKey', reason: 'Fixture candidate.' }],
            coverage: 'partial',
            warnings: [],
          },
          {
            claimId: 'SEC-CLAIM-002',
            candidateLocations: [],
            coverage: 'none',
            warnings: [{ code: 'no-candidate-location', path: '/mappings/1/candidateLocations', message: 'No candidate source location was found.' }],
          },
        ],
        summary: { totalClaims: 2, mappedClaims: 1, totalCandidateLocations: 1, totalWarnings: 1, byCoverage: { none: 1, partial: 1, full: 0 } },
        provenance: { origin: 'deterministic', generator: 'test', claims: 'claims.json', scope: 'scope.json', target: 'target' },
        warnings: [],
      });
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.ts'],
        outOfScope: [],
        trustBoundaries: [{ id: 'TB-001', name: 'api', entryPoints: ['api'], attackerControlled: true }],
      });
      writeJson(localResponsesPath, {
        schemaVersion: 'security-audit-response-fixture/v1',
        responses: [
          { taskId: 'SEC-AUDIT-TASK-001', result: 'finding', finding: { status: 'confirmed', title: 'Normalized status', summary: 'Fixture finding.' } },
          { taskId: 'SEC-AUDIT-TASK-002', result: 'no-finding', rationale: 'No proof gap was found for this claim.' },
        ],
      });

      const result = await generateSecurityProofAudit(localClaimsPath, localCodeMapPath, localScopePath, outDir, {
        generatedAt,
        responseFixture: localResponsesPath,
      });

      expect(result.taskBundle.summary.byStatus).toEqual({ ready: 1, blockedNoCandidateLocation: 1, blockedMissingCodeMap: 0 });
      expect(result.responseSummary).toEqual({ totalResponses: 2, findingResponses: 1, noFindingResponses: 1, missingResponses: 0 });
      expect(result.findings?.findings).toHaveLength(1);
      expect(result.findings?.findings[0]['status']).toBe('candidate');
      expect(result.warnings).toEqual(expect.arrayContaining([expect.objectContaining({ code: 'finding-status-normalized' })]));
      expect(readFileSync(join(outDir, 'security-audit-summary.md'), 'utf8')).toContain('SEC-AUDIT-TASK-002 / SEC-CLAIM-002: no-finding');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });


  it('allows response fixtures where every task has no finding', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-proof-audit-all-clean-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-proof-audit-all-clean-out-'));
    try {
      const localResponsesPath = join(fixtureDir, 'responses.json');
      writeJson(localResponsesPath, {
        schemaVersion: 'security-audit-response-fixture/v1',
        responses: [
          { taskId: 'SEC-AUDIT-TASK-001', result: 'no-finding', rationale: 'The fixture proof established the claim for the mapped code path.' },
        ],
      });

      const result = await generateSecurityProofAudit(claimsPath, codeMapPath, scopePath, outDir, {
        generatedAt,
        responseFixture: localResponsesPath,
      });

      expect(result.findings).toBeUndefined();
      expect(result.outputPaths.findings).toBeUndefined();
      expect(result.responseSummary).toEqual({ totalResponses: 1, findingResponses: 0, noFindingResponses: 1, missingResponses: 0 });
      expect(readFileSync(join(outDir, 'security-audit-summary.md'), 'utf8')).toContain('SEC-AUDIT-TASK-001 / SEC-CLAIM-001: no-finding');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('exposes proof-attempt audit through ae security audit', () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-proof-audit-cli-'));
    try {
      const result = spawnSync(
        tsxBin,
        [
          'src/cli/index.ts',
          'security',
          'audit',
          '--claims',
          claimsPath,
          '--code-map',
          codeMapPath,
          '--scope',
          scopePath,
          '--out',
          outDir,
          '--response-fixture',
          responseFixturePath,
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
      expect(result.stdout).toContain('Security proof-attempt audit completed');
      expect(result.stdout).toContain('Findings: 2');
      expect(readJson<{ schemaVersion: string }>(join(outDir, 'security-audit-tasks.json')).schemaVersion).toBe('security-audit-task-bundle/v1');
      expect(readJson<{ findings: unknown[] }>(join(outDir, 'security-findings.json')).findings).toHaveLength(2);
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });
});
