import { describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';

const scriptPath = resolve('scripts/verify/render-codex-summary.mjs');
const tmpRoot = resolve('.codex-local/tmp');

const runWithModelReport = (payload: unknown) => {
  mkdirSync(tmpRoot, { recursive: true });
  const dir = mkdtempSync(join(tmpRoot, 'render-codex-formal-'));
  mkdirSync(join(dir, 'artifacts', 'codex'), { recursive: true });
  writeFileSync(
    join(dir, 'artifacts', 'codex', 'model-check.json'),
    `${JSON.stringify(payload, null, 2)}\n`,
    'utf8',
  );
  const result = spawnSync(process.execPath, [scriptPath], { cwd: dir, encoding: 'utf8' });
  const markdown = readFileSync(join(dir, 'codex-summary.md'), 'utf8');
  return { dir, result, markdown };
};

describe('Codex model-check summary rendering', () => {
  it('renders not-run as an explicit non-success execution status', () => {
    const run = runWithModelReport({
      schemaVersion: 'model-check-report/v1',
      artifactStatus: 'execution-report',
      status: 'not-run',
      ok: null,
      tlc: { results: [], skipped: ['No .tla found'], errors: [] },
      alloy: { results: [], skipped: ['No .als found'], errors: [] },
    });
    try {
      expect(run.result.status).toBe(0);
      expect(run.markdown).toContain('status=not-run, executed=0, failed=0, toolErrors=0, timeouts=0, ok=n/a');
      expect(run.markdown).not.toContain('Model Checking: 0 properties');
    } finally {
      rmSync(run.dir, { recursive: true, force: true });
    }
  });

  it('does not interpret a legacy pseudo artifact as execution evidence', () => {
    const run = runWithModelReport({
      specificationId: 'spec_synthetic',
      satisfied: true,
      properties: [{ name: 'Safety', satisfied: true }],
    });
    try {
      expect(run.result.status).toBe(0);
      expect(run.markdown).toContain('unrecognized contract (not counted as execution evidence)');
      expect(run.markdown).not.toContain('Unsatisfied: 0');
    } finally {
      rmSync(run.dir, { recursive: true, force: true });
    }
  });
});
