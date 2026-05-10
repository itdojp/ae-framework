import { describe, expect, it } from 'vitest';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, relative, resolve } from 'node:path';

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
        'claim-level-summary.json',
        'policy-decision-js-v1.json',
        'policy-gate-summary.json',
        'change-package-v2.json',
        'change-package-v2.md',
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

      const claimLevel = JSON.parse(readFileSync(join(outputDir, 'claim-level-summary.json'), 'utf8'));
      expect(claimLevel.schemaVersion).toBe('claim-level-summary/v1');
      expect(claimLevel.summary).toMatchObject({
        totalClaims: 3,
        modelChecked: 1,
        runtimeMitigated: 1,
        waived: 1,
        reportOnlyDecisions: 3,
      });
      const noNegativeBalance = claimLevel.claims.find(
        (claim: { claimId: string }) => claim.claimId === 'no-negative-balance',
      );
      expect(noNegativeBalance).toBeDefined();
      expect(noNegativeBalance).toMatchObject({
        state: 'model-checked',
        missingEvidenceRefs: [
          expect.objectContaining({
            id: 'change-package-v2:no-negative-balance:target-a3:achieved-a2',
          }),
        ],
      });

      // Post-roadmap canonical route regression:
      // claim-level-summary/v1 -> policy-decision/v1 -> change-package/v2
      // must keep waived / runtime-mitigated / partial states reviewable without
      // promoting legacy compatibility routes to canonical summary inputs.
      const changePackage = JSON.parse(readFileSync(join(outputDir, 'change-package-v2.json'), 'utf8'));
      expect(changePackage.schemaVersion).toBe('change-package/v2');
      expect(changePackage.assurance).toMatchObject({
        targetLevel: 'A3',
        achievedLevel: 'A2',
        status: 'partial',
      });
      expect(changePackage.policyDecision).toMatchObject({
        present: true,
        sourceArtifactPath: 'artifacts/assurance-e2e/inventory-waiver/policy-decision-js-v1.json',
        result: 'waived',
        mode: 'report-only',
        enforced: false,
      });
      expect(changePackage.claims).toEqual(expect.arrayContaining([
        expect.objectContaining({ id: 'no-negative-balance', status: 'model-checked' }),
        expect.objectContaining({ id: 'manual-fraud-review', status: 'waived' }),
      ]));
      expect(changePackage.releaseControls.postDeployChecks).toContain(
        'post-deploy-verify workflow or release verification artifact required before production rollout',
      );
      expect(changePackage.releaseControls.rollbackSignals).toContain('golden-artifact-drift');
      expect(changePackage.residualRisks).toEqual(expect.arrayContaining([
        expect.objectContaining({ id: 'claim:manual-fraud-review:waived', claimIds: ['manual-fraud-review'] }),
      ]));

      const changePackageMarkdown = readFileSync(join(outputDir, 'change-package-v2.md'), 'utf8');
      expect(changePackageMarkdown).toContain('changed requirement refs: REQ-INV-001, REQ-INV-002');
      expect(changePackageMarkdown).toContain('claim states: satisfied=0, tested=0, model-checked=1');
      expect(changePackageMarkdown).toContain('waived=1');
      expect(changePackageMarkdown).toContain('### Release / Post-deploy Controls');
      expect(changePackageMarkdown).toContain('### Residual Risks');
      expect(changePackageMarkdown).toContain('### Waivers');
      expect(changePackageMarkdown).not.toContain('formal/summary.json');
      expect(changePackageMarkdown).not.toContain('quality:scorecard');
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

  it('derives policy changed files from the selected scenario directory', () => {
    mkdirSync(resolve(repoRoot, 'artifacts'), { recursive: true });
    const testRoot = mkdtempSync(join(resolve(repoRoot, 'artifacts'), 'assurance-e2e-custom-test-'));
    const scenarioDir = join(testRoot, 'custom-inventory-waiver');
    const outputDir = join(testRoot, 'actual');

    try {
      cpSync(resolve(repoRoot, 'fixtures/assurance-e2e/inventory-waiver'), scenarioDir, { recursive: true });
      const result = runScript([
        '--scenario-dir',
        scenarioDir,
        '--output-dir',
        outputDir,
        '--no-compare',
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const policyInput = JSON.parse(readFileSync(join(outputDir, 'policy-input-v1.json'), 'utf8'));
      expect(policyInput.changedFiles).toContain(
        relative(repoRoot, join(scenarioDir, 'inputs/change-package-v2.json')).split('\\').join('/'),
      );
      expect(policyInput.changedFiles).not.toContain(
        'fixtures/assurance-e2e/inventory-waiver/inputs/change-package-v2.json',
      );
    } finally {
      rmSync(testRoot, { recursive: true, force: true });
    }
  });

  it('rejects output directories outside the repository root with a clear error', () => {
    const outsideOutputDir = resolve(repoRoot, '..', 'assurance-e2e-outside-repo-output');

    try {
      const result = runScript([
        '--scenario',
        'inventory-waiver',
        '--output-dir',
        outsideOutputDir,
        '--no-compare',
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('output-dir must stay under the repository root');
    } finally {
      rmSync(outsideOutputDir, { recursive: true, force: true });
    }
  });
});
