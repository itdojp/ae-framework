import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateClaimEvidenceManifestSemantics } from '../../scripts/ci/lib/claim-evidence-manifest-contract.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/assurance/build-claim-evidence-manifest.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

const runScript = (args: string[]) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
  });

const writeJson = (targetPath: string, payload: unknown) => {
  writeFileSync(targetPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
};

const buildSchemaValidator = () => {
  const schema = JSON.parse(readFileSync(resolve(repoRoot, 'schema/claim-evidence-manifest.schema.json'), 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe.sequential('claim evidence manifest generator', () => {
  it('parses arguments and generates a schema-valid JSON plus Markdown manifest', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      assuranceSummary: 'artifacts/assurance/assurance-summary.json',
      outputJson: 'artifacts/assurance/claim-evidence-manifest.json',
      outputMd: 'artifacts/assurance/claim-evidence-manifest.md',
      validate: true,
    });
    expect(() => mod.parseArgs(['--assurance-summary'])).toThrow('--assurance-summary requires a value');

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-claim-evidence-manifest-'));
    const outputJson = join(sandbox, 'claim-evidence-manifest.json');
    const outputMd = join(sandbox, 'claim-evidence-manifest.md');

    try {
      const result = runScript([
        '--assurance-summary',
        'fixtures/assurance/sample.assurance-summary.json',
        '--change-package',
        'fixtures/change-package/sample.change-package-v2.json',
        '--quality-scorecard',
        'fixtures/quality/sample.quality-scorecard.json',
        '--generated-at',
        '2026-04-28T18:20:00.000Z',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('[claim-evidence-manifest] wrote');

      const manifest = JSON.parse(readFileSync(outputJson, 'utf8'));
      const validate = buildSchemaValidator();
      expect(validate(manifest), JSON.stringify(validate.errors)).toBe(true);
      expect(validateClaimEvidenceManifestSemantics(manifest)).toEqual([]);
      expect(manifest).toMatchObject({
        schemaVersion: 'claim-evidence-manifest/v1',
        generatedAt: '2026-04-28T18:20:00.000Z',
        summary: {
          totalClaims: 2,
          fullySupported: 1,
          partiallySupported: 1,
          waived: 0,
          unresolved: 0,
        },
      });
      expect(manifest.sourceArtifacts).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ id: 'assurance-summary', present: true, required: true }),
          expect.objectContaining({ id: 'change-package-v2', present: true, schemaVersion: 'change-package/v2' }),
          expect.objectContaining({ id: 'quality-scorecard', present: true, schemaVersion: 'quality-scorecard/v1' }),
        ]),
      );

      const stockClaim = manifest.claims.find((claim: { id: string }) => claim.id === 'no-negative-stock');
      expect(stockClaim).toMatchObject({
        targetLevel: 'A2',
        achievedLevel: 'A2',
        status: 'satisfied',
      });
      expect(stockClaim.evidenceRefs).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ sourceArtifactId: 'assurance-summary', kind: 'behavior' }),
          expect.objectContaining({ sourceArtifactId: 'quality-scorecard', kind: 'quality' }),
        ]),
      );

      const balanceClaim = manifest.claims.find((claim: { id: string }) => claim.id === 'no-negative-balance');
      expect(balanceClaim).toMatchObject({
        targetLevel: 'A3',
        achievedLevel: 'A2',
        status: 'partial',
      });
      expect(balanceClaim.proofObligationRefs).toEqual([
        expect.objectContaining({ id: 'obl-1', status: 'discharged', method: 'tla' }),
      ]);
      expect(balanceClaim.missingEvidenceRefs.length).toBeGreaterThan(0);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('# Claim Evidence Manifest');
      expect(markdown).toContain('| no-negative-balance | high | A3 | A2 | partial |');
      expect(markdown).toContain('## Missing evidence');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects change-package v2 references to claims that are not anchored by source claims', () => {
    const fixture = JSON.parse(
      readFileSync(resolve(repoRoot, 'fixtures/change-package/sample.change-package-v2.json'), 'utf8'),
    );
    const cases = [
      {
        label: 'proof obligation',
        mutate: (payload: typeof fixture) => {
          payload.proofObligations[0].claimId = 'phantom-claim';
        },
        expectedContext: 'proofObligations[0].claimId',
      },
      {
        label: 'counterexample',
        mutate: (payload: typeof fixture) => {
          payload.counterexamples[0].claimIds = ['phantom-claim'];
        },
        expectedContext: 'counterexamples[0].claimIds',
      },
      {
        label: 'waiver',
        mutate: (payload: typeof fixture) => {
          payload.waivers = [
            {
              owner: '@team-risk',
              expires: '2026-06-30',
              reason: 'Orphan waiver should not create a synthetic claim.',
              relatedClaimIds: ['phantom-claim'],
            },
          ];
        },
        expectedContext: 'waivers[0].relatedClaimIds',
      },
    ];

    for (const testCase of cases) {
      const sandbox = mkdtempSync(join(tmpdir(), `ae-claim-evidence-manifest-orphan-${testCase.label}-`));
      const changePackagePath = join(sandbox, 'change-package-v2.json');
      const outputJson = join(sandbox, 'claim-evidence-manifest.json');
      const outputMd = join(sandbox, 'claim-evidence-manifest.md');

      try {
        const payload = structuredClone(fixture);
        testCase.mutate(payload);
        writeJson(changePackagePath, payload);

        const result = runScript([
          '--assurance-summary',
          'fixtures/assurance/sample.assurance-summary.json',
          '--change-package',
          changePackagePath,
          '--quality-scorecard',
          'fixtures/quality/sample.quality-scorecard.json',
          '--generated-at',
          '2026-04-28T18:20:00.000Z',
          '--output-json',
          outputJson,
          '--output-md',
          outputMd,
        ]);

        expect(result.status, result.stderr || result.stdout).toBe(1);
        expect(result.stderr).toContain(testCase.expectedContext);
        expect(result.stderr).toContain("references unknown claim 'phantom-claim'");
      } finally {
        rmSync(sandbox, { recursive: true, force: true });
      }
    }
  });
});
