import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

// Traceability anchors for #2732:
// REQ-UCP-002 REQ-UCP-004
// DGM-ASIS-TOBE-PROMOTION MOR-EMIT AT-UPSTREAM-TRACE-PRESERVED
const repoRoot = resolve('.');
const contextPackFixture = 'fixtures/context-pack/upstream-context-promotion-minimal.yaml';
const discoveryPackFixture = 'fixtures/discovery-pack/upstream-context-promotion-minimal.yaml';
const assuranceProfile = 'spec/assurance-profile/upstream-context-promotion-v1.json';

const runNode = (script: string, args: string[]) =>
  spawnSync(process.execPath, [resolve(repoRoot, script), ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
  });

describe('upstream-context-promotion assurance aggregate', () => {
  it('aggregates all five claims with supporting upstream promotion evidence', () => {
    const reportDir = mkdtempSync(join(tmpdir(), 'upstream-context-promotion-assurance-'));

    try {
      const contextPackReport = join(reportDir, 'context-pack-validate-report.json');
      const naturalReport = join(reportDir, 'natural-report.json');
      const productReport = join(reportDir, 'product-report.json');
      const boundaryReport = join(reportDir, 'boundary-report.json');

      expect(runNode('scripts/context-pack/validate.mjs', [
        '--sources',
        contextPackFixture,
        '--schema',
        'schema/context-pack-v1.schema.json',
        '--discovery-pack',
        discoveryPackFixture,
        '--report-json',
        contextPackReport,
        '--report-md',
        join(reportDir, 'context-pack-validate-report.md'),
      ]).status).toBe(0);

      expect(runNode('scripts/context-pack/verify-natural-transformation.mjs', [
        '--map',
        'fixtures/context-pack/upstream-context-promotion-minimal-natural-transformation.json',
        '--schema',
        'schema/context-pack-natural-transformation.schema.json',
        '--context-pack-sources',
        contextPackFixture,
        '--report-json',
        naturalReport,
        '--report-md',
        join(reportDir, 'natural-report.md'),
      ]).status).toBe(0);

      expect(runNode('scripts/context-pack/verify-product-coproduct.mjs', [
        '--map',
        'fixtures/context-pack/upstream-context-promotion-minimal-product-coproduct.json',
        '--schema',
        'schema/context-pack-product-coproduct.schema.json',
        '--context-pack-sources',
        contextPackFixture,
        '--report-json',
        productReport,
        '--report-md',
        join(reportDir, 'product-report.md'),
      ]).status).toBe(0);

      expect(runNode('scripts/context-pack/verify-boundary-map.mjs', [
        '--map',
        'fixtures/context-pack/upstream-context-promotion-minimal-boundary-map.json',
        '--schema',
        'schema/context-pack-boundary-map.schema.json',
        '--context-pack-sources',
        contextPackFixture,
        '--report-json',
        boundaryReport,
        '--report-md',
        join(reportDir, 'boundary-report.md'),
      ]).status).toBe(0);

      writeFileSync(
        join(reportDir, 'verify-lite-run-summary.json'),
        `${JSON.stringify({
          artifacts: {
            contextPackReportJson: contextPackReport,
            contextPackNaturalTransformationReportJson: naturalReport,
            contextPackProductCoproductReportJson: productReport,
          },
        }, null, 2)}\n`,
        'utf8',
      );

      writeFileSync(
        join(reportDir, 'evidence-manifest.json'),
        `${JSON.stringify({
          schemaVersion: 'assurance-evidence-manifest/v1',
          entries: [
            {
              lane: 'spec',
              kind: 'boundary-map',
              sourceKind: 'spec-derived',
              claimIds: ['boundary-separation-explicit'],
              artifactPath: boundaryReport,
              generatorLineage: 'upstream-context-promotion-fixture',
              detail: 'boundary map validation passed',
            },
          ],
        }, null, 2)}\n`,
        'utf8',
      );

      const outputJson = join(reportDir, 'assurance-summary.json');
      const outputMd = join(reportDir, 'assurance-summary.md');
      const aggregateResult = runNode('scripts/assurance/aggregate-lanes.mjs', [
        '--assurance-profile',
        assuranceProfile,
        '--context-pack',
        contextPackFixture,
        '--verify-lite-summary',
        join(reportDir, 'verify-lite-run-summary.json'),
        '--evidence-manifest',
        join(reportDir, 'evidence-manifest.json'),
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(aggregateResult.status).toBe(0);
      const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
      expect(summary.summary.claimCount).toBe(5);
      expect(summary.summary.satisfiedClaims).toBe(5);
      expect(summary.summary.warningClaims).toBe(0);
      expect(summary.claims.map((claim: { claimId: string }) => claim.claimId)).toEqual([
        'approved-upstream-only-promoted',
        'behavior-preserving-transformation-modeled',
        'boundary-separation-explicit',
        'input-normalization-variants-covered',
        'upstream-trace-preserved',
      ]);
    } finally {
      rmSync(reportDir, { recursive: true, force: true });
    }
  });
});
