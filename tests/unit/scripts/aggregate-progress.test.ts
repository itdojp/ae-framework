import { describe, it, expect } from 'vitest';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';

const scriptPath = resolve('scripts/progress/aggregate-progress.mjs');

const runScript = (cwd: string, env: Record<string, string>) => {
  return spawnSync('node', [scriptPath], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env }
  });
};

const readJson = (p: string) => JSON.parse(readFileSync(p, 'utf8'));

describe('aggregate-progress', () => {
  it('aggregates progress, quality, metrics, and traceability', () => {
    const dir = mkdtempSync(join(tmpdir(), 'progress-summary-'));
    const metricsDir = join(dir, 'metrics');
    const qualityDir = join(dir, 'reports', 'quality-gates');
    const phaseDir = join(dir, '.ae');

    mkdirSync(metricsDir, { recursive: true });
    mkdirSync(qualityDir, { recursive: true });
    mkdirSync(phaseDir, { recursive: true });

    writeFileSync(join(metricsDir, 'project-metrics.json'), JSON.stringify({
      projectName: 'demo',
      sessionId: 'session-1',
      tddCompliance: 95,
      overallCoverage: 88,
      totalViolations: 1,
      phases: [{ endTime: '2025-01-01T00:00:00Z' }, {}]
    }));

    writeFileSync(join(qualityDir, 'quality-report-ci-latest.json'), JSON.stringify({
      environment: 'ci',
      overallScore: 90,
      totalGates: 10,
      passedGates: 9,
      failedGates: 1,
      summary: { blockers: ['Gate A'] }
    }));

    writeFileSync(join(dir, 'traceability.json'), JSON.stringify({
      total: 4,
      testsLinked: 2,
      implLinked: 3,
      formalLinked: 1
    }));

    writeFileSync(join(phaseDir, 'phase-state.json'), JSON.stringify({
      projectId: 'proj-1',
      createdAt: '2025-01-01T00:00:00Z',
      updatedAt: '2025-01-01T00:00:00Z',
      currentPhase: 'test',
      approvalsRequired: true,
      phaseStatus: {
        intent: { completed: true, artifacts: [] },
        formal: { completed: true, artifacts: [] },
        test: { completed: false, artifacts: [] },
        code: { completed: false, artifacts: [] },
        verify: { completed: false, artifacts: [] },
        operate: { completed: false, artifacts: [] }
      }
    }));

    const outputPath = join(dir, 'artifacts', 'progress', 'summary.json');
    const result = runScript(dir, { PROGRESS_SUMMARY_OUTPUT: outputPath });

    expect(result.status).toBe(0);
    const summary = readJson(outputPath);
    expect(summary.progress?.percent).toBe(33);
    expect(summary.quality?.environment).toBe('ci');
    expect(summary.metrics?.projectName).toBe('demo');
    expect(summary.traceability?.coverage?.tests).toBe(0.5);
    expect(summary.missing).toEqual([]);

    rmSync(dir, { recursive: true, force: true });
  });

  it('honors AE_PHASE_STATE_ROOT fallback', () => {
    const dir = mkdtempSync(join(tmpdir(), 'progress-phase-root-'));
    const stateRoot = join(dir, 'state-root');
    mkdirSync(join(stateRoot, '.ae'), { recursive: true });

    writeFileSync(join(stateRoot, '.ae', 'phase-state.json'), JSON.stringify({
      projectId: 'proj-2',
      createdAt: '2025-01-01T00:00:00Z',
      updatedAt: '2025-01-01T00:00:00Z',
      currentPhase: 'intent',
      approvalsRequired: false,
      phaseStatus: {
        intent: { completed: false, artifacts: [] },
        formal: { completed: false, artifacts: [] },
        test: { completed: false, artifacts: [] },
        code: { completed: false, artifacts: [] },
        verify: { completed: false, artifacts: [] },
        operate: { completed: false, artifacts: [] }
      }
    }));

    const outputPath = join(dir, 'artifacts', 'progress', 'summary.json');
    const result = runScript(dir, {
      AE_PHASE_STATE_ROOT: stateRoot,
      PROGRESS_SUMMARY_OUTPUT: outputPath
    });

    expect(result.status).toBe(0);
    const summary = readJson(outputPath);
    expect(summary.sources.phaseState).toBe('state-root/.ae/phase-state.json');
    expect(summary.progress?.currentPhase).toBe('intent');

    rmSync(dir, { recursive: true, force: true });
  });

  it('reports missing sources when inputs are absent', () => {
    const dir = mkdtempSync(join(tmpdir(), 'progress-missing-'));
    const outputPath = join(dir, 'artifacts', 'progress', 'summary.json');

    const result = runScript(dir, { PROGRESS_SUMMARY_OUTPUT: outputPath });

    expect(result.status).toBe(0);
    const summary = readJson(outputPath);
    const missing = new Set(summary.missing);
    expect(missing.has('metrics')).toBe(true);
    expect(missing.has('quality')).toBe(true);
    expect(missing.has('traceability')).toBe(true);
    expect(missing.has('phaseState')).toBe(true);

    rmSync(dir, { recursive: true, force: true });
  });
});
