import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/assurance/aggregate-claim-levels.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;
const fixtureRoot = 'fixtures/assurance/claim-level-summary';

const buildStableTestEnv = () => {
  const env = { ...process.env };
  delete env.GITHUB_BASE_REF;
  delete env.GITHUB_HEAD_REF;
  delete env.GITHUB_SHA;
  return {
    ...env,
    NODE_OPTIONS: '',
  };
};

const runScript = (args: string[]) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
    env: buildStableTestEnv(),
  });

const readJson = (targetPath: string) => JSON.parse(readFileSync(resolve(repoRoot, targetPath), 'utf8'));

const buildSchemaValidator = () => {
  const schema = readJson('schema/claim-level-summary-v1.schema.json');
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe.sequential('claim-level summary aggregator', () => {
  it('parses arguments and exposes deterministic defaults', async () => {
    const mod = await import(moduleUrl);

    expect(mod.parseArgs([])).toMatchObject({
      claimEvidenceManifest: 'artifacts/assurance/claim-evidence-manifest.json',
      policyGateSummary: 'artifacts/ci/policy-gate-summary.json',
      changePackage: 'artifacts/change-package/change-package-v2.json',
      temporaryOverrides: [],
      outputJson: 'artifacts/assurance/claim-level-summary.json',
      outputMd: 'artifacts/assurance/claim-level-summary.md',
      validate: true,
    });
    expect(() => mod.parseArgs(['--claim-evidence-manifest'])).toThrow('--claim-evidence-manifest requires a value');
    expect(() => mod.parseArgs(['--pr-number', '0'])).toThrow('--pr-number must be a positive integer');
    expect(mod.parseArgs(['--', '--help'])).toMatchObject({ help: true });
  });

  it('generates the golden claim-level JSON and Markdown projection', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-claim-level-summary-'));
    const outputJson = join(sandbox, 'claim-level-summary.json');
    const outputMd = join(sandbox, 'claim-level-summary.md');

    try {
      const result = runScript([
        '--claim-evidence-manifest',
        `${fixtureRoot}/inputs/claim-evidence-manifest.json`,
        '--policy-gate-summary',
        `${fixtureRoot}/inputs/policy-gate-summary.json`,
        '--change-package',
        `${fixtureRoot}/inputs/change-package-v2.json`,
        '--temporary-override',
        `${fixtureRoot}/inputs/temporary-overrides/override-manual-waiver-2026-06.json`,
        '--generated-at',
        '2026-05-08T00:00:00.000Z',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('[claim-level-summary] wrote');

      const actual = JSON.parse(readFileSync(outputJson, 'utf8'));
      const expected = readJson(`${fixtureRoot}/expected/claim-level-summary.json`);
      expect(actual).toEqual(expected);
      expect(readFileSync(outputMd, 'utf8')).toBe(
        readFileSync(resolve(repoRoot, `${fixtureRoot}/expected/claim-level-summary.md`), 'utf8'),
      );

      const validate = buildSchemaValidator();
      expect(validate(actual), JSON.stringify(validate.errors)).toBe(true);
      expect(actual.summary).toMatchObject({
        totalClaims: 9,
        satisfied: 1,
        tested: 1,
        modelChecked: 1,
        proved: 1,
        runtimeMitigated: 1,
        waived: 1,
        unresolved: 1,
        failed: 1,
        notApplicable: 1,
        enforcedDecisions: 0,
        reportOnlyDecisions: 9,
      });
      expect(new Set(actual.claims.map((claim: { state: string }) => claim.state))).toEqual(
        new Set([
          'satisfied',
          'tested',
          'model-checked',
          'proved',
          'runtime-mitigated',
          'waived',
          'unresolved',
          'failed',
          'not-applicable',
        ]),
      );

      const failedClaim = actual.claims.find((claim: { claimId: string }) => claim.claimId === 'strict-proof-failure');
      expect(failedClaim.decision).toMatchObject({ mode: 'report-only', result: 'report-only', enforced: false });
      expect(failedClaim.evidenceRefs.some((ref: { status: string }) => ref.status === 'failed')).toBe(true);

      const runtimeClaim = actual.claims.find((claim: { claimId: string }) => claim.claimId === 'rollout-runtime');
      expect(runtimeClaim.runtimeControls).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ id: 'alert:rollout_guard_violation', kind: 'alert' }),
          expect.objectContaining({ id: 'feature-flag:staged_release_guard', kind: 'feature-flag' }),
        ]),
      );

      const notApplicableClaim = actual.claims.find((claim: { claimId: string }) => claim.claimId === 'ui-out-of-scope');
      expect(notApplicableClaim.applicability).toMatchObject({
        reason: 'UI-only animation claim is outside the backend release scope.',
        scope: 'backend release',
        artifactPath: 'docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md',
      });
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('is deterministic for the same inputs and can run without a policy-gate summary', async () => {
    const mod = await import(moduleUrl);
    const commonOptions = {
      claimEvidenceManifest: `${fixtureRoot}/inputs/claim-evidence-manifest.json`,
      policyGateSummary: 'fixtures/assurance/claim-level-summary/inputs/missing-policy-gate-summary.json',
      changePackage: `${fixtureRoot}/inputs/change-package-v2.json`,
      temporaryOverrides: [`${fixtureRoot}/inputs/temporary-overrides/override-manual-waiver-2026-06.json`],
      generatedAt: '2026-05-08T00:00:00.000Z',
      repository: null,
      prNumber: null,
      baseRef: null,
      headRef: null,
      headSha: null,
      outputJson: 'unused.json',
      outputMd: 'unused.md',
      schema: 'schema/claim-level-summary-v1.schema.json',
      validate: true,
      help: false,
    };

    const first = mod.buildClaimLevelSummary(commonOptions);
    const second = mod.buildClaimLevelSummary(commonOptions);
    expect(second).toEqual(first);
    expect(first.inputs.policyGateSummary).toMatchObject({ present: false, required: false, path: null });
    expect(first.claims.find((claim: { claimId: string }) => claim.claimId === 'strict-proof-failure').state).toBe('unresolved');
    expect(first.claims.every((claim: { decision: { mode: string; enforced: boolean } }) => (
      claim.decision.mode === 'report-only' && claim.decision.enforced === false
    ))).toBe(true);
  });
});
