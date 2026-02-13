import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { describe, expect, it, vi } from 'vitest';
import {
  SCHEMA_VERSION,
  buildRunContext,
  buildRunUrl,
  emitAutomationReport,
} from '../../../scripts/ci/lib/automation-report.mjs';

describe('automation-report', () => {
  it('builds run URL from GitHub Actions environment', () => {
    const url = buildRunUrl({
      GITHUB_SERVER_URL: 'https://github.com',
      GITHUB_REPOSITORY: 'itdojp/ae-framework',
      GITHUB_RUN_ID: '12345',
    });
    expect(url).toBe('https://github.com/itdojp/ae-framework/actions/runs/12345');
  });

  it('builds run context with parsed numeric fields', () => {
    const run = buildRunContext({
      GITHUB_WORKFLOW: 'PR Self-Heal',
      GITHUB_EVENT_NAME: 'workflow_dispatch',
      GITHUB_RUN_ID: '999',
      GITHUB_RUN_ATTEMPT: '2',
      GITHUB_SERVER_URL: 'https://github.com',
      GITHUB_REPOSITORY: 'itdojp/ae-framework',
      GITHUB_REF: 'refs/heads/main',
      GITHUB_SHA: 'abc',
    });
    expect(run.workflow).toBe('PR Self-Heal');
    expect(run.event).toBe('workflow_dispatch');
    expect(run.runId).toBe(999);
    expect(run.attempt).toBe(2);
    expect(run.url).toContain('/actions/runs/999');
  });

  it('emits JSON report, writes file, and appends step summary', () => {
    const tmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'automation-report-test-'));
    const reportFile = path.join(tmpRoot, 'report', 'result.json');
    const summaryFile = path.join(tmpRoot, 'summary.md');
    const logs: string[] = [];
    const spy = vi.spyOn(console, 'log').mockImplementation((line?: unknown) => {
      logs.push(String(line));
    });

    try {
      const report = emitAutomationReport({
        tool: 'pr-self-heal',
        status: 'resolved',
        reason: 'all checks passed',
        prNumber: 42,
        mode: 'dry-run',
        metrics: {
          processed: 1,
        },
      }, {
        GITHUB_STEP_SUMMARY: summaryFile,
        GITHUB_SERVER_URL: 'https://github.com',
        GITHUB_REPOSITORY: 'itdojp/ae-framework',
        GITHUB_RUN_ID: '555',
        AE_AUTOMATION_REPORT_FILE: reportFile,
      });

      expect(report.schemaVersion).toBe(SCHEMA_VERSION);
      expect(report.run.url).toBe('https://github.com/itdojp/ae-framework/actions/runs/555');
      expect(fs.existsSync(reportFile)).toBe(true);
      expect(fs.readFileSync(reportFile, 'utf8')).toContain('"tool": "pr-self-heal"');
      expect(fs.readFileSync(summaryFile, 'utf8')).toContain('## Automation Report');
      expect(logs.some((line) => line.includes('[ae-automation-report]'))).toBe(true);
    } finally {
      spy.mockRestore();
      fs.rmSync(tmpRoot, { recursive: true, force: true });
    }
  });
});

