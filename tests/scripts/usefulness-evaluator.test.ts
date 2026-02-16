import { describe, it, expect, beforeAll } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

let parseArgs: (argv: string[]) => any;
let evaluateUsefulness: (payload: any) => any;
let runUsefulness: (options: any, deps?: any) => number;

beforeAll(async () => {
  ({ parseArgs, evaluateUsefulness, runUsefulness } = await import('../../scripts/evaluation/evaluate-usefulness.mjs'));
});

describe('usefulness evaluator args', () => {
  it('parses threshold and explicit inputs', () => {
    const options = parseArgs([
      'node',
      'scripts/evaluation/evaluate-usefulness.mjs',
      '--run-index',
      'artifacts/runs/custom-index.json',
      '--min-score',
      '80',
      '--strict-inputs',
    ]);

    expect(options.runIndex).toBe('artifacts/runs/custom-index.json');
    expect(options.minScore).toBe(80);
    expect(options.strictInputs).toBe(true);
    expect(options.provided.runIndex).toBe(true);
    expect(options.argErrors).toEqual([]);
    expect(options.unknown).toEqual([]);
  });

  it('ignores standalone -- separator', () => {
    const options = parseArgs([
      'node',
      'scripts/evaluation/evaluate-usefulness.mjs',
      '--',
      '--min-score',
      '75',
    ]);
    expect(options.minScore).toBe(75);
    expect(options.unknown).toEqual([]);
  });
});

describe('usefulness evaluator scoring', () => {
  it('computes all four axes and overall score', () => {
    const report = evaluateUsefulness({
      runIndex: {
        runs: [
          { status: 'success' },
          { status: 'failed' },
          { status: 'success' },
        ],
      },
      traceability: {
        total: 10,
        testsLinked: 8,
        implLinked: 7,
        formalLinked: 5,
      },
      verifyProfile: {
        steps: [
          { name: 'build', required: true, status: 'passed' },
          { name: 'verify:lite', required: true, status: 'failed' },
          { name: 'mbt', required: false, status: 'skipped' },
        ],
      },
      qualityReport: {
        overallScore: 88,
      },
      runManifestCheck: {
        ok: false,
        violations: [{ kind: 'stale_artifact' }],
      },
      inputStatus: [],
    });

    expect(report.axes.reproducibility.score).toBe(67);
    expect(report.axes.traceability.score).toBe(67);
    expect(report.axes.automation.score).toBe(55);
    expect(report.axes.qualityDetection.score).toBe(89);
    expect(report.overall.score).toBe(70);
    expect(report.overall.missingAxes).toEqual([]);
  });
});

describe('usefulness evaluator execution', () => {
  it('returns exit 2 when explicit input path is missing', () => {
    const tmp = mkdtempSync(path.join(tmpdir(), 'ae-usefulness-missing-'));
    try {
      const options = parseArgs([
        'node',
        'scripts/evaluation/evaluate-usefulness.mjs',
        '--run-index',
        'not-found.json',
      ]);
      const exitCode = runUsefulness(options, { cwd: tmp, logger: { log() {}, error() {} } });
      expect(exitCode).toBe(2);
    } finally {
      rmSync(tmp, { recursive: true, force: true });
    }
  });

  it('writes reports and returns exit 1 when min-score is not met', () => {
    const tmp = mkdtempSync(path.join(tmpdir(), 'ae-usefulness-threshold-'));
    try {
      mkdirSync(path.join(tmp, 'artifacts', 'runs'), { recursive: true });
      mkdirSync(path.join(tmp, 'artifacts'), { recursive: true });
      writeFileSync(
        path.join(tmp, 'artifacts', 'runs', 'index.json'),
        JSON.stringify({
          runs: [
            { status: 'success' },
            { status: 'failed' },
          ],
        }, null, 2),
        'utf8',
      );
      writeFileSync(
        path.join(tmp, 'traceability.json'),
        JSON.stringify({
          total: 5,
          testsLinked: 4,
          implLinked: 3,
          formalLinked: 2,
        }, null, 2),
        'utf8',
      );
      writeFileSync(
        path.join(tmp, 'artifacts', 'verify-profile-summary.json'),
        JSON.stringify({
          steps: [
            { name: 'build', required: true, status: 'passed' },
            { name: 'verify:lite', required: true, status: 'passed' },
            { name: 'pbt', required: false, status: 'skipped' },
          ],
        }, null, 2),
        'utf8',
      );
      writeFileSync(
        path.join(tmp, 'artifacts', 'run-manifest-check.json'),
        JSON.stringify({ ok: true, violations: [] }, null, 2),
        'utf8',
      );

      const options = parseArgs([
        'node',
        'scripts/evaluation/evaluate-usefulness.mjs',
        '--min-score',
        '95',
      ]);
      const exitCode = runUsefulness(options, { cwd: tmp, logger: { log() {}, error() {} } });
      expect(exitCode).toBe(1);

      const jsonReportPath = path.join(tmp, 'artifacts', 'evaluation', 'ae-framework-usefulness-latest.json');
      const mdReportPath = path.join(tmp, 'artifacts', 'evaluation', 'ae-framework-usefulness-latest.md');
      const jsonReport = JSON.parse(readFileSync(jsonReportPath, 'utf8'));
      const markdownReport = readFileSync(mdReportPath, 'utf8');

      expect(jsonReport.schemaVersion).toBe('usefulness-evaluation/v1');
      expect(typeof jsonReport.overall.score).toBe('number');
      expect(markdownReport).toContain('# AE Framework Usefulness Evaluation');
    } finally {
      rmSync(tmp, { recursive: true, force: true });
    }
  });
});
