import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import {
  executeActionableTasks,
  normalizeExecutionResults,
} from '../../../scripts/ci/lib/actionable-task-executor.mjs';

const tempDirs: string[] = [];

function createTempDir(prefix: string) {
  const dir = mkdtempSync(path.join(os.tmpdir(), prefix));
  tempDirs.push(dir);
  return dir;
}

function createExecutorScript(body: string) {
  const dir = createTempDir('ae-actionable-exec-');
  const scriptPath = path.join(dir, 'executor.js');
  writeFileSync(scriptPath, body, 'utf8');
  return scriptPath;
}

afterEach(() => {
  for (const dir of tempDirs.splice(0)) {
    rmSync(dir, { recursive: true, force: true });
  }
});

describe('actionable-task-executor', () => {
  it('normalizes execution results and fills missing entries as failed', () => {
    const tasks = [{ commentId: 101 }, { commentId: 102 }, { commentId: 103 }];
    const normalized = normalizeExecutionResults([
      { commentId: 101, status: 'ok' },
      { commentId: 102, status: 'skip', reason: 'not applicable' },
    ], tasks);
    expect(normalized).toEqual([
      { commentId: 101, status: 'success', reason: '' },
      { commentId: 102, status: 'skipped', reason: 'not applicable' },
      { commentId: 103, status: 'failed', reason: 'missing execution result for actionable task' },
    ]);
  });

  it('returns failed summary when command is not configured', () => {
    const summary = executeActionableTasks([{ commentId: 101 }], {
      dryRun: false,
      command: '',
    });
    expect(summary.status).toBe('failed');
    expect(summary.failed).toBe(1);
    expect(summary.results[0].reason).toContain('AE_AUTOPILOT_ACTIONABLE_COMMAND');
  });

  it('executes command and parses JSON output', () => {
    const scriptPath = createExecutorScript(
      [
        "const fs = require('node:fs');",
        "const payload = JSON.parse(fs.readFileSync(process.env.AE_ACTIONABLE_TASKS_JSON, 'utf8'));",
        "const results = (payload.tasks || []).map((task) => ({ commentId: task.commentId, status: 'success' }));",
        'process.stdout.write(JSON.stringify({ results }));',
      ].join('\n'),
    );

    const summary = executeActionableTasks([{ commentId: 201 }, { commentId: 202 }], {
      dryRun: false,
      command: `node ${scriptPath}`,
      prNumber: 999,
      round: 2,
    });

    expect(summary.status).toBe('success');
    expect(summary.attempted).toBe(2);
    expect(summary.succeeded).toBe(2);
    expect(summary.failed).toBe(0);
  });

  it('supports JSON output on the last stdout line', () => {
    const scriptPath = createExecutorScript(
      [
        "const fs = require('node:fs');",
        "const payload = JSON.parse(fs.readFileSync(process.env.AE_ACTIONABLE_TASKS_JSON, 'utf8'));",
        "const first = payload.tasks[0]?.commentId;",
        "console.log('executor log line');",
        "process.stdout.write(JSON.stringify({ results: [{ commentId: first, status: 'success' }] }));",
      ].join('\n'),
    );

    const summary = executeActionableTasks([{ commentId: 301 }], {
      dryRun: false,
      command: `node ${scriptPath}`,
    });
    expect(summary.status).toBe('success');
    expect(summary.succeeded).toBe(1);
  });
});
