import { describe, it, expect } from 'vitest';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';

const scriptPath = resolve('scripts/progress/render-progress-summary.mjs');

const runScript = (cwd: string, env: Record<string, string>) => {
  return spawnSync('node', [scriptPath], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env }
  });
};

describe('render-progress-summary', () => {
  it('renders progress summary with deltas when previous is provided', () => {
    const dir = mkdtempSync(join(tmpdir(), 'render-progress-'));
    const progressDir = join(dir, 'artifacts', 'progress');
    mkdirSync(progressDir, { recursive: true });

    const current = {
      progress: { percent: 50, currentPhase: 'test', phasesCompleted: 3, phasesTotal: 6 },
      quality: { environment: 'ci', overallScore: 85, passedGates: 8, totalGates: 10, blockers: [] },
      metrics: { tddCompliance: 92, overallCoverage: 80, totalViolations: 2 },
      traceability: { total: 4, coverage: { tests: 0.5, impl: 0.75, formal: 0.25 } }
    };
    const previous = {
      progress: { percent: 40 },
      quality: { overallScore: 80 },
      metrics: { tddCompliance: 90, overallCoverage: 78, totalViolations: 3 },
      traceability: { coverage: { tests: 0.4, impl: 0.6, formal: 0.2 } }
    };

    const currentPath = join(progressDir, 'summary.json');
    const previousPath = join(progressDir, 'summary.prev.json');
    const outputPath = join(progressDir, 'PR_PROGRESS.md');
    writeFileSync(currentPath, JSON.stringify(current, null, 2));
    writeFileSync(previousPath, JSON.stringify(previous, null, 2));

    const result = runScript(dir, {
      PROGRESS_SUMMARY_PATH: currentPath,
      PROGRESS_SUMMARY_PREVIOUS: previousPath,
      PROGRESS_SUMMARY_MD: outputPath
    });

    expect(result.status).toBe(0);
    const md = readFileSync(outputPath, 'utf8');
    expect(md).toContain('Progress Summary');
    expect(md).toContain('Δ +10%');
    expect(md).toContain('tests=50% (Δ +10%)');
    expect(md).toContain('Traceability');

    rmSync(dir, { recursive: true, force: true });
  });

  it('exits with error when summary is missing', () => {
    const dir = mkdtempSync(join(tmpdir(), 'render-progress-missing-'));
    const outputPath = join(dir, 'artifacts', 'progress', 'PR_PROGRESS.md');

    const result = runScript(dir, {
      PROGRESS_SUMMARY_PATH: join(dir, 'missing.json'),
      PROGRESS_SUMMARY_MD: outputPath
    });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('progress summary not found');

    rmSync(dir, { recursive: true, force: true });
  });

  it('exits with error when summary is invalid JSON', () => {
    const dir = mkdtempSync(join(tmpdir(), 'render-progress-invalid-'));
    const progressDir = join(dir, 'artifacts', 'progress');
    mkdirSync(progressDir, { recursive: true });
    const summaryPath = join(progressDir, 'summary.json');
    const outputPath = join(progressDir, 'PR_PROGRESS.md');
    writeFileSync(summaryPath, '{ invalid json }');

    const result = runScript(dir, {
      PROGRESS_SUMMARY_PATH: summaryPath,
      PROGRESS_SUMMARY_MD: outputPath
    });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('progress summary is invalid JSON');

    rmSync(dir, { recursive: true, force: true });
  });
});
