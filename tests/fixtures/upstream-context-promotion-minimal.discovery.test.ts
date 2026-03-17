import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';

// Traceability anchors for #2732:
// REQ-UCP-001 REQ-UCP-003 REQ-UCP-005 REQ-UCP-006 REQ-UCP-007
// DGM-ASIS-TOBE-PROMOTION MOR-NORMALIZE AT-ONLY-APPROVED-PROMOTED
const repoRoot = resolve('.');
const validateScript = resolve(repoRoot, 'scripts/discovery-pack/validate.mjs');
const compileScript = resolve(repoRoot, 'scripts/discovery-pack/compile.mjs');
const schemaPath = resolve(repoRoot, 'schema/discovery-pack-v1.schema.json');
const fixturePath = 'fixtures/discovery-pack/upstream-context-promotion-minimal.yaml';
const contextPackSchemaPath = resolve(repoRoot, 'schema/context-pack-v1.schema.json');

const runNode = (script: string, args: string[]) =>
  spawnSync(process.execPath, [script, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
  });

describe('upstream-context-promotion discovery fixture', () => {
  it('validates strict-approved and compiles both targets from approved elements only', () => {
    const outputDir = mkdtempSync(join(tmpdir(), 'upstream-context-promotion-discovery-'));

    try {
      const validateResult = runNode(validateScript, [
        '--sources',
        fixturePath,
        '--schema',
        schemaPath,
        '--output-dir',
        outputDir,
        '--strict-approved',
      ]);
      expect(validateResult.status).toBe(0);

      const validateReport = JSON.parse(
        readFileSync(join(outputDir, 'discovery-pack-validate-report.json'), 'utf8'),
      );
      expect(validateReport.status).toBe('pass');
      expect(validateReport.summary.strictApprovedViolations).toBe(0);
      expect(validateReport.summary.unresolvedTraceRefs).toBe(0);

      const planSpecResult = runNode(compileScript, [
        '--target',
        'plan-spec',
        '--sources',
        fixturePath,
        '--schema',
        schemaPath,
        '--output-dir',
        outputDir,
      ]);
      expect(planSpecResult.status).toBe(0);

      const planSpec = readFileSync(join(outputDir, 'plan-to-spec-normalized.md'), 'utf8');
      expect(planSpec).toContain('Only approved discovery elements are eligible for compile and promotion.');
      expect(planSpec).not.toContain('Require explicit override for non-approved promotion');

      const compileReport = JSON.parse(
        readFileSync(join(outputDir, 'discovery-pack-compile-report.json'), 'utf8'),
      );
      expect(compileReport.target).toBe('plan-spec');
      expect(compileReport.summary.excludedByStatusCount).toBeGreaterThan(0);

      const scaffoldResult = runNode(compileScript, [
        '--target',
        'context-pack-scaffold',
        '--sources',
        fixturePath,
        '--schema',
        schemaPath,
        '--output-dir',
        outputDir,
      ]);
      expect(scaffoldResult.status).toBe(0);

      const scaffold = yaml.parse(readFileSync(join(outputDir, 'context-pack-scaffold.yaml'), 'utf8'));
      expect(scaffold.generated_from.discovery_pack.source_file).toBe(fixturePath);
      expect(scaffold.generated_from.selected_ids.requirements).toEqual([
        'DRQ-UPSTREAM-TRACE',
        'DRQ-APPROVED-ONLY',
        'DRQ-NORMALIZE-INPUT',
      ]);

      const contextPackSchema = JSON.parse(readFileSync(contextPackSchemaPath, 'utf8'));
      const ajv = new Ajv2020({ allErrors: true, strict: false });
      addFormats(ajv);
      expect(ajv.compile(contextPackSchema)(scaffold)).toBe(true);
    } finally {
      rmSync(outputDir, { recursive: true, force: true });
    }
  });
});
