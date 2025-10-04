import { describe, it, expect } from 'vitest';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const runScript = (summaryPath?: string) => {
  const args = summaryPath ? [summaryPath] : [];
  return spawnSync('node', ['scripts/ci/render-generate-artifacts-summary.mjs', ...args], {
    cwd: process.cwd(),
    encoding: 'utf8'
  });
};

describe('render-generate-artifacts-summary', () => {
  it('prints generated timestamp and truncates long file lists', () => {
    const dir = mkdtempSync(join(tmpdir(), 'render-summary-'));
    const summaryPath = join(dir, 'summary.json');
    const files = Array.from({ length: 12 }, (_, index) => ({
      status: index % 2 === 0 ? 'A' : 'M',
      file: `docs/file-${index}.md`
    }));
    writeFileSync(summaryPath, JSON.stringify({
      generatedAt: '2025-01-01T00:00:00Z',
      targets: [
        { path: 'docs/notes', hasChanges: true, files },
        { path: 'templates/example', hasChanges: false }
      ]
    }));

    const result = runScript(summaryPath);

    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Generated at: 2025-01-01T00:00:00Z');
    expect(result.stdout).toContain('- docs/notes: CHANGED');
    expect(result.stdout).toContain('- templates/example: clean');
    expect(result.stdout.split('\n').filter((line) => line.includes('•')).length).toBe(11);
    expect(result.stdout).toContain('  • … (2 more)');

    rmSync(dir, { recursive: true, force: true });
  });

  it('exits with error when summary cannot be parsed', () => {
    const dir = mkdtempSync(join(tmpdir(), 'render-summary-invalid-'));
    const summaryPath = join(dir, 'summary.json');
    writeFileSync(summaryPath, 'not-json');

    const result = runScript(summaryPath);

    expect(result.status).toBe(1);
    expect(result.stdout).toContain('Failed to read diff summary');

    rmSync(dir, { recursive: true, force: true });
  });

  it('alerts when no path is provided', () => {
    const result = runScript();

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('usage: render-generate-artifacts-summary.mjs');
  });
});
