import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { mkdtempSync, readdirSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
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

  beforeEach(() => {
    tempDir = mkdtempSync(join(tmpdir(), 'quality-report-output-'));
  });

  afterEach(() => {
    rmSync(tempDir, { recursive: true, force: true });
  });

  it('writes history + latest by default', async () => {
    const runner = new QualityGateRunner();
    const report = createSampleReport();

    await (runner as unknown as {
      saveReport: (r: QualityReport, dir: string, options?: { noHistory?: boolean }) => Promise<void>;
    }).saveReport(report, tempDir);

    const files = readdirSync(tempDir);
    expect(files).toContain('quality-report-development-latest.json');
    expect(hasHistoryReportFile(files)).toBe(true);

    const latest = JSON.parse(readFileSync(join(tempDir, 'quality-report-development-latest.json'), 'utf8'));
    expect(latest.environment).toBe('development');
  });

  it('writes latest only when --no-history equivalent is enabled', async () => {
    const runner = new QualityGateRunner();
    const report = createSampleReport();

    await (runner as unknown as {
      saveReport: (r: QualityReport, dir: string, options?: { noHistory?: boolean }) => Promise<void>;
    }).saveReport(report, tempDir, { noHistory: true });

    const files = readdirSync(tempDir);
    expect(files).toContain('quality-report-development-latest.json');
    expect(hasHistoryReportFile(files)).toBe(false);
  });
});
