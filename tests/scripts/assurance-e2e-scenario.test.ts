import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/assurance/run-e2e-scenario.mjs');

const runScript = (args: string[]) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
  });

describe('assurance e2e scenario runner', () => {
  it('reproduces the inventory waiver golden artifacts', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputDir = mkdtempSync(join(resolve(repoRoot, 'artifacts'), 'assurance-e2e-test-'));

    try {
      const result = runScript([
        '--scenario',
        'inventory-waiver',
        '--output-dir',
        outputDir,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('policy assurance result: waived');
      for (const fileName of [
        'verify-lite-run-summary.json',
        'assurance-summary.json',
        'claim-evidence-manifest.json',
        'policy-decision-js-v1.json',
        'policy-gate-summary.json',
      ]) {
        expect(existsSync(join(outputDir, fileName)), `${fileName} should be generated`).toBe(true);
      }

      const manifest = JSON.parse(readFileSync(join(outputDir, 'claim-evidence-manifest.json'), 'utf8'));
      expect(manifest.summary).toMatchObject({
        totalClaims: 3,
        fullySupported: 1,
        partiallySupported: 1,
        waived: 1,
      });

      const decision = JSON.parse(readFileSync(join(outputDir, 'policy-decision-js-v1.json'), 'utf8'));
      expect(decision.evaluation.assurance).toMatchObject({
        mode: 'report-only',
        result: 'waived',
        summary: {
          pass: 1,
          waived: 1,
          reportOnly: 1,
          activeWaivers: 1,
        },
      });
    } finally {
      rmSync(outputDir, { recursive: true, force: true });
    }
  });

  it('reports drift when expected artifacts differ from actual output', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const outputDir = mkdtempSync(join(resolve(repoRoot, 'artifacts'), 'assurance-e2e-drift-test-'));

    try {
      const result = runScript([
        '--scenario',
        'inventory-waiver',
        '--generated-at',
        '2026-05-07T00:00:00.000Z',
        '--output-dir',
        outputDir,
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('assurance e2e scenario drift detected');
      expect(result.stderr).toContain('claim-evidence-manifest.json');
    } finally {
      rmSync(outputDir, { recursive: true, force: true });
    }
  });
});
