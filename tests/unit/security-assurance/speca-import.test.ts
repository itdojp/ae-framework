import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { importSpecaLikeSecurityArtifacts } from '../../../src/security/assurance/speca-import.js';

const inputDir = 'fixtures/security-assurance/speca-like-input';
const generatedAt = '2026-05-07T00:00:00.000Z';
const tsxBin = resolve('node_modules/.bin/tsx');

const readJson = <T>(path: string): T => JSON.parse(readFileSync(path, 'utf8')) as T;

const writeJson = (filePath: string, value: unknown) => {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

describe('SPECA-compatible security import', () => {
  it('converts the SPECA-like fixture into schema-valid security assurance artifacts', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-speca-import-'));
    try {
      const result = await importSpecaLikeSecurityArtifacts(inputDir, outDir, { generatedAt });

      expect(result.artifacts.claims).toEqual(
        expect.objectContaining({
          schemaVersion: 'security-claim/v1',
          generatedAt,
          summary: {
            totalClaims: 1,
            byCriticality: { low: 0, medium: 0, high: 1, critical: 0 },
          },
        }),
      );
      expect(result.artifacts.claims.claims[0]).toEqual(
        expect.objectContaining({
          id: 'SEC-CLAIM-001',
          provenance: expect.objectContaining({ origin: 'imported', generator: 'speca-compatible-import' }),
        }),
      );
      expect(result.artifacts.threatModel.threats[0]).toEqual(
        expect.objectContaining({
          relatedClaimIds: ['SEC-CLAIM-001'],
          stride: 'Tampering',
          cwe: 'CWE-20',
        }),
      );
      expect(result.artifacts.findings.findings[0]).toEqual(
        expect.objectContaining({
          id: 'SEC-FINDING-001',
          claimId: 'SEC-CLAIM-001',
          status: 'candidate',
        }),
      );
      expect(result.artifacts.review.reviews[0]).toEqual(
        expect.objectContaining({
          findingId: 'SEC-FINDING-001',
          result: 'needs-human-review',
          falsePositiveRootCause: null,
        }),
      );

      expect(result.warnings.map((entry) => entry.code)).toEqual(
        expect.arrayContaining(['unsupported-field', 'root-cause-dropped']),
      );
      expect(existsSync(join(outDir, 'security-claims.json'))).toBe(true);
      expect(existsSync(join(outDir, 'security-threat-model.json'))).toBe(true);
      expect(existsSync(join(outDir, 'security-findings.json'))).toBe(true);
      expect(existsSync(join(outDir, 'security-review.json'))).toBe(true);
      expect(readFileSync(join(outDir, 'import-summary.md'), 'utf8')).toContain('Warnings:');
      const summary = readJson<{ counts: { warnings: number }; warnings: Array<{ path: string }> }>(join(outDir, 'import-summary.json'));
      expect(summary.counts.warnings).toBe(result.warnings.length);
      expect(summary.warnings.some((entry) => entry.path.includes('specaPhaseNote'))).toBe(true);
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('exposes the import through ae security import-speca', () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-speca-import-cli-'));
    try {
      const result = spawnSync(
        tsxBin,
        [
          'src/cli/index.ts',
          'security',
          'import-speca',
          '--input',
          inputDir,
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
      expect(result.stdout).toContain('SPECA-compatible security import completed');
      expect(result.stdout).toContain('Warnings:');
      expect(readJson<{ schemaVersion: string }>(join(outDir, 'security-review.json')).schemaVersion).toBe('security-review/v1');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('preserves explicit canonical IDs and avoids generated ID collisions', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-speca-collision-input-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-speca-collision-out-'));
    try {
      writeJson(join(fixtureDir, '01e_security_properties.json'), {
        properties: [
          {
            id: 'SP-001',
            type: 'invariant',
            statement: 'Imported property without a canonical claim id.',
            source: { uri: 'spec/security/a.md' },
            stride: ['Tampering'],
            cwe: ['CWE-20'],
            trustBoundary: { id: 'TB-001', entryPoints: ['api'], attackerControlled: true },
          },
          {
            id: 'SEC-CLAIM-001',
            type: 'invariant',
            statement: 'Imported property with an explicit canonical claim id.',
            source: { uri: 'spec/security/b.md' },
            stride: ['Tampering'],
            cwe: ['CWE-20'],
            trustBoundary: { id: 'TB-001', entryPoints: ['api'], attackerControlled: true },
          },
        ],
      });
      writeJson(join(fixtureDir, '02c_threats.json'), {
        threats: [
          { id: 'T-1', propertyId: 'SP-001', stride: 'Tampering', cwe: 'CWE-20', description: 'Threat A' },
          { id: 'T-2', claimId: 'SEC-CLAIM-001', stride: 'Tampering', cwe: 'CWE-20', description: 'Threat B' },
        ],
      });
      writeJson(join(fixtureDir, '03_audit_findings.json'), {
        findings: [
          {
            id: 'SPECA-FINDING-001',
            propertyId: 'SP-001',
            severity: 'high',
            confidence: 'medium',
            title: 'Finding A',
            summary: 'Finding A summary',
            affectedLocations: [{ path: 'src/a.ts', startLine: 1, endLine: 2 }],
          },
          {
            id: 'SEC-FINDING-001',
            claimId: 'SEC-CLAIM-001',
            severity: 'medium',
            confidence: 'medium',
            title: 'Finding B',
            summary: 'Finding B summary',
            affectedLocations: [{ path: 'src/b.ts', startLine: 3, endLine: 4 }],
            evidenceRefs: [
              {
                id: 'EVIDENCE-B',
                kind: 'custom-kind',
                path: 'outputs/custom.json',
                rawScore: 0.5,
              },
            ],
          },
        ],
      });
      writeJson(join(fixtureDir, '04_review_gates.json'), {
        reviews: [
          { findingId: 'SPECA-FINDING-001', result: 'needs-human-review', gates: {} },
          { findingId: 'SEC-FINDING-001', result: 'needs-human-review', gates: {} },
        ],
      });

      const result = await importSpecaLikeSecurityArtifacts(fixtureDir, outDir, { generatedAt });

      expect(result.artifacts.claims.claims.map((claim) => claim.id)).toEqual(['SEC-CLAIM-002', 'SEC-CLAIM-001']);
      expect(result.artifacts.threatModel.threats.map((threat) => threat.relatedClaimIds)).toEqual([
        ['SEC-CLAIM-002'],
        ['SEC-CLAIM-001'],
      ]);
      expect(result.artifacts.findings.findings.map((finding) => finding.id)).toEqual(['SEC-FINDING-002', 'SEC-FINDING-001']);
      expect(result.artifacts.review.reviews.map((review) => review.findingId)).toEqual(['SEC-FINDING-002', 'SEC-FINDING-001']);
      expect(result.warnings).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ code: 'id-collision-normalized', path: '/properties/0/id' }),
          expect.objectContaining({ code: 'id-collision-normalized', path: '/findings/0/id' }),
          expect.objectContaining({ code: 'unsupported-field', path: '/findings/1/evidenceRefs/0/rawScore' }),
          expect.objectContaining({ code: 'unsupported-value', path: '/findings/1/evidenceRefs/0/kind' }),
        ]),
      );
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('resolves bundled schemas when the CLI runs outside the repository root', () => {
    const cwd = mkdtempSync(join(tmpdir(), 'ae-speca-outside-cwd-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-speca-outside-out-'));
    try {
      const result = spawnSync(
        tsxBin,
        [
          resolve('src/cli/index.ts'),
          'security',
          'import-speca',
          '--input',
          resolve(inputDir),
          '--out',
          outDir,
          '--generated-at',
          generatedAt,
        ],
        {
          cwd,
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
      expect(readJson<{ schemaVersion: string }>(join(outDir, 'security-claims.json')).schemaVersion).toBe('security-claim/v1');
    } finally {
      rmSync(cwd, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('renders repo-relative POSIX paths in import summaries', async () => {
    const outDir = join('artifacts', `speca-import-test-${Date.now()}`);
    mkdirSync(outDir, { recursive: true });
    try {
      await importSpecaLikeSecurityArtifacts(inputDir, outDir, { generatedAt });
      const summary = readJson<{ source: string; outputs: Record<string, string> }>(join(outDir, 'import-summary.json'));

      expect(summary.source).toBe('fixtures/security-assurance/speca-like-input');
      expect(Object.values(summary.outputs).every((value) => !value.includes('\\'))).toBe(true);
      expect(summary.outputs.claims).toBe(`${outDir}/security-claims.json`);
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });
});
