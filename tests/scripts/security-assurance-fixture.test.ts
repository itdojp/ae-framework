import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/security/run-security-assurance-fixture.mjs');

const runScript = (args: string[]) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 180_000,
  });

describe('security assurance fixture runner', () => {
  it('reproduces the cache-key golden artifacts', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputDir = mkdtempSync(join(resolve(repoRoot, 'artifacts'), 'security-assurance-fixture-test-'));

    try {
      const result = runScript([
        '--scenario',
        'cache-key',
        '--output-dir',
        outputDir,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('comparison: ok');
      for (const fileName of [
        'security-claims.json',
        'security-code-map.json',
        'security-audit-tasks.json',
        'security-findings.json',
        'security-review.json',
        'assurance-summary.json',
        'claim-evidence-manifest.json',
        'security-summary.md',
      ]) {
        expect(existsSync(join(outputDir, fileName)), `${fileName} should be generated`).toBe(true);
      }

      const claims = JSON.parse(readFileSync(join(outputDir, 'security-claims.json'), 'utf8'));
      expect(claims.summary).toMatchObject({ totalClaims: 3 });

      const findings = JSON.parse(readFileSync(join(outputDir, 'security-findings.json'), 'utf8'));
      expect(findings.summary).toMatchObject({
        totalFindings: 2,
        byStatus: { candidate: 2 },
        bySeverity: { high: 1, low: 1 },
      });

      const review = JSON.parse(readFileSync(join(outputDir, 'security-review.json'), 'utf8'));
      expect(review.summary.byResult).toMatchObject({
        needsHumanReview: 1,
        outOfScope: 1,
      });

      const manifest = JSON.parse(readFileSync(join(outputDir, 'claim-evidence-manifest.json'), 'utf8'));
      expect(manifest.summary.security).toMatchObject({
        claims: 3,
        findings: 2,
        reviews: 2,
        needsHumanReview: 1,
        outOfScope: 1,
        highOrCriticalOpen: 1,
      });
    } finally {
      rmSync(outputDir, { recursive: true, force: true });
    }
  });


  it('reports when expected comparison is intentionally skipped', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputDir = mkdtempSync(join(resolve(repoRoot, 'artifacts'), 'security-assurance-fixture-no-compare-test-'));

    try {
      const result = runScript([
        '--scenario',
        'cache-key',
        '--output-dir',
        outputDir,
        '--no-compare',
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('comparison: skipped');
    } finally {
      rmSync(outputDir, { recursive: true, force: true });
    }
  });

  it('reports drift when deterministic timestamp changes', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputDir = mkdtempSync(join(resolve(repoRoot, 'artifacts'), 'security-assurance-fixture-drift-test-'));

    try {
      const result = runScript([
        '--scenario',
        'cache-key',
        '--generated-at',
        '2026-05-08T00:00:00.000Z',
        '--output-dir',
        outputDir,
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('security assurance fixture drift detected');
      expect(result.stderr).toContain('security-claims.json');
    } finally {
      rmSync(outputDir, { recursive: true, force: true });
    }
  });
});
