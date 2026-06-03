import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { QualityGateRunner } from '../../src/quality/quality-gate-runner.js';
import type { QualityReport } from '../../src/quality/policy-loader.js';

const createSampleReport = (): QualityReport => ({
  timestamp: '2026-02-16T00:00:00.000Z',
  environment: 'development',
  overallScore: 100,
  totalGates: 1,
  passedGates: 1,
  failedGates: 0,
  results: [],
  summary: {
    byCategory: {},
    executionTime: 10,
    blockers: [],
  },
});

const hasHistoryReportFile = (files: string[]) =>
  files.some((name) => /^quality-report-development-(?!latest).*\.json$/.test(name));

  describe('QualityGateRunner report output options', () => {
    let tempDir: string;
    let previousWorkspaceRoot: string | undefined;

    beforeEach(() => {
      previousWorkspaceRoot = process.env['AE_WORKSPACE_ROOT'];
      tempDir = [
        'artifacts',
        'quality',
        `quality-report-output-${Date.now()}-${Math.random().toString(16).slice(2)}`,
      ].join('/');
      mkdirSync(join(process.cwd(), tempDir), { recursive: true });
    });

    afterEach(() => {
      if (previousWorkspaceRoot === undefined) {
        delete process.env['AE_WORKSPACE_ROOT'];
      } else {
        process.env['AE_WORKSPACE_ROOT'] = previousWorkspaceRoot;
      }
      rmSync(join(process.cwd(), tempDir), { recursive: true, force: true });
    });

  it('writes history + latest by default', async () => {
    const runner = new QualityGateRunner();
    const report = createSampleReport();

    await (runner as unknown as {
      saveReport: (r: QualityReport, dir: string, options?: { noHistory?: boolean }) => Promise<void>;
    }).saveReport(report, tempDir);

    const files = readdirSync(join(process.cwd(), tempDir));
    expect(files).toContain('quality-report-development-latest.json');
    expect(hasHistoryReportFile(files)).toBe(true);

    const latest = JSON.parse(readFileSync(join(process.cwd(), tempDir, 'quality-report-development-latest.json'), 'utf8'));
    expect(latest.environment).toBe('development');
  });

    it('writes latest only when --no-history equivalent is enabled', async () => {
      const runner = new QualityGateRunner();
      const report = createSampleReport();

    await (runner as unknown as {
      saveReport: (r: QualityReport, dir: string, options?: { noHistory?: boolean }) => Promise<void>;
    }).saveReport(report, tempDir, { noHistory: true });

      const files = readdirSync(join(process.cwd(), tempDir));
      expect(files).toContain('quality-report-development-latest.json');
      expect(hasHistoryReportFile(files)).toBe(false);
    });

    it('uses the resolved workspace-root anchored path for report writes', async () => {
      const runner = new QualityGateRunner();
      const report = createSampleReport();
      const workspaceRoot = process.cwd();
      const outputDir = `${tempDir}/anchored-reports`;
      process.env['AE_WORKSPACE_ROOT'] = workspaceRoot;
      const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

      try {
        await (runner as unknown as {
          saveReport: (r: QualityReport, dir: string, options?: { noHistory?: boolean }) => Promise<void>;
        }).saveReport(report, outputDir, { noHistory: true });

        const latestPath = join(workspaceRoot, outputDir, 'quality-report-development-latest.json');
        expect(existsSync(latestPath)).toBe(true);
        expect(consoleLogSpy.mock.calls.flat().join('\n')).toContain(latestPath);
      } finally {
        consoleLogSpy.mockRestore();
      }
    });
  });
