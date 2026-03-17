import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const contextPackFixture = 'fixtures/context-pack/upstream-context-promotion-minimal.yaml';
const discoveryPackFixture = 'fixtures/discovery-pack/upstream-context-promotion-minimal.yaml';

const runNode = (script: string, args: string[]) =>
  spawnSync(process.execPath, [resolve(repoRoot, script), ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
  });

describe('upstream-context-promotion context-pack fixtures', () => {
  it('validates context-pack upstream refs and all supporting maps', () => {
    const reportDir = mkdtempSync(join(tmpdir(), 'upstream-context-promotion-context-pack-'));

    try {
      const contextPackResult = runNode('scripts/context-pack/validate.mjs', [
        '--sources',
        contextPackFixture,
        '--schema',
        'schema/context-pack-v1.schema.json',
        '--discovery-pack',
        discoveryPackFixture,
        '--report-json',
        join(reportDir, 'context-pack-validate-report.json'),
        '--report-md',
        join(reportDir, 'context-pack-validate-report.md'),
      ]);
      expect(contextPackResult.status).toBe(0);
      const contextPackReport = JSON.parse(readFileSync(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
      expect(contextPackReport.status).toBe('pass');
      expect(contextPackReport.warnings).toEqual([]);

      const naturalResult = runNode('scripts/context-pack/verify-natural-transformation.mjs', [
        '--map',
        'fixtures/context-pack/upstream-context-promotion-minimal-natural-transformation.json',
        '--schema',
        'schema/context-pack-natural-transformation.schema.json',
        '--context-pack-sources',
        contextPackFixture,
        '--report-json',
        join(reportDir, 'natural.json'),
        '--report-md',
        join(reportDir, 'natural.md'),
      ]);
      expect(naturalResult.status).toBe(0);
      expect(JSON.parse(readFileSync(join(reportDir, 'natural.json'), 'utf8')).status).toBe('pass');

      const productResult = runNode('scripts/context-pack/verify-product-coproduct.mjs', [
        '--map',
        'fixtures/context-pack/upstream-context-promotion-minimal-product-coproduct.json',
        '--schema',
        'schema/context-pack-product-coproduct.schema.json',
        '--context-pack-sources',
        contextPackFixture,
        '--report-json',
        join(reportDir, 'product.json'),
        '--report-md',
        join(reportDir, 'product.md'),
      ]);
      expect(productResult.status).toBe(0);
      expect(JSON.parse(readFileSync(join(reportDir, 'product.json'), 'utf8')).status).toBe('pass');

      const boundaryResult = runNode('scripts/context-pack/verify-boundary-map.mjs', [
        '--map',
        'fixtures/context-pack/upstream-context-promotion-minimal-boundary-map.json',
        '--schema',
        'schema/context-pack-boundary-map.schema.json',
        '--context-pack-sources',
        contextPackFixture,
        '--report-json',
        join(reportDir, 'boundary.json'),
        '--report-md',
        join(reportDir, 'boundary.md'),
      ]);
      expect(boundaryResult.status).toBe(0);
      const boundaryReport = JSON.parse(readFileSync(join(reportDir, 'boundary.json'), 'utf8'));
      expect(boundaryReport.status).toBe('pass');
      expect(boundaryReport.summary.totalViolations).toBe(0);
    } finally {
      rmSync(reportDir, { recursive: true, force: true });
    }
  });
});
