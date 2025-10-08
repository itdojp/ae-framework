import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import os from 'node:os';

const scriptPath = join(process.cwd(), 'scripts/trace/import-dashboard.mjs');

describe('import-dashboard CLI', () => {
  it('shows help', () => {
    const result = spawnSync(process.execPath, [scriptPath, '--help'], { encoding: 'utf8' });
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Usage:');
  });

  it('fails when token is missing', () => {
    const result = spawnSync(process.execPath, [scriptPath, '--input', 'dummy.json'], { encoding: 'utf8' });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('missing Grafana API token');
  });

  it('fails when folder id is invalid', () => {
    const result = spawnSync(process.execPath, [scriptPath, '--token', 'fake', '--folder-id', 'abc'], { encoding: 'utf8' });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('invalid folder id');
  });

  it('fails when dashboard JSON is malformed', () => {
    const tempDir = mkdtempSync(join(os.tmpdir(), 'import-dashboard-'));
    const invalidFile = join(tempDir, 'invalid.json');
    writeFileSync(invalidFile, '{not json');
    const result = spawnSync(process.execPath, [scriptPath, '--token', 'fake', '--input', invalidFile], { encoding: 'utf8' });
    try {
      expect(result.status).toBe(1);
      expect(result.stderr).toContain('malformed JSON');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
