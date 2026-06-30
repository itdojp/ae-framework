import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, rmSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  collectCodeQualityBaseline,
  parseArgs,
} from '../../scripts/quality/collect-code-quality-baseline.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/quality/collect-code-quality-baseline.mjs');
const outputDir = resolve(repoRoot, '.codex-local/tmp/code-quality-baseline-test');

function resetOutputDir() {
  rmSync(outputDir, { recursive: true, force: true });
  mkdirSync(outputDir, { recursive: true });
}

describe('collect-code-quality-baseline', () => {
  it('builds a deterministic report-only baseline from configured repository surfaces', () => {
    const options = parseArgs(['--repo-root', repoRoot]);
    const report = collectCodeQualityBaseline(options);

    expect(report.schemaVersion).toBe('quality-baseline/v1');
    expect(report.contractId).toBe('quality-baseline.v1');
    expect(report.generatedAt).toBe('1970-01-01T00:00:00.000Z');
    expect(report.enforcement.mode).toBe('report-only');
    expect(report.enforcement.ordinaryPrBlocking).toBe(false);
    expect(report.architecturePlanes.map((plane) => plane.plane).sort()).toEqual([
      'Control',
      'Evidence',
      'Execution',
      'Observability',
      'Policy',
    ]);
    expect(report.qualityChecks.map((check) => check.id)).toEqual([
      'types-check',
      'lint',
      'test-fast',
      'doc-consistency',
      'validate-json',
    ]);
    expect(report.qualityChecks.every((check) => check.status === 'configured')).toBe(true);
    expect(report.publicEntrypoints.publicScripts.map((entry) => entry.name)).toContain('quality:baseline');
    expect(report.publicEntrypoints.publicScripts.map((entry) => entry.name)).toContain('context-pack:validate');
    expect(report.debtLedger.path).toBe('docs/quality/code-quality-debt-ledger.json');
    expect(report.debtLedger.exceptionCount).toBeGreaterThanOrEqual(1);
    expect(report.topCleanupCandidates.some((candidate) => candidate.id === 'quality-scorecard-legacy-route')).toBe(true);
  });

  it('writes JSON and Markdown artifacts without adding an enforcement gate', () => {
    resetOutputDir();
    const jsonPath = join(outputDir, 'baseline.json');
    const markdownPath = join(outputDir, 'baseline.md');

    const result = spawnSync('node', [
      scriptPath,
      '--output-json',
      jsonPath,
      '--output-md',
      markdownPath,
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(existsSync(jsonPath)).toBe(true);
    expect(existsSync(markdownPath)).toBe(true);

    const report = JSON.parse(readFileSync(jsonPath, 'utf8'));
    expect(report.enforcement.mode).toBe('report-only');
    expect(report.enforcement.ordinaryPrBlocking).toBe(false);
    expect(readFileSync(markdownPath, 'utf8')).toContain('Ordinary PR blocking: **no**');
  });
});
