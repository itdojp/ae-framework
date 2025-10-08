import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';

const scriptPath = join(process.cwd(), 'scripts/trace/export-dashboard.mjs');

describe('export-dashboard CLI', () => {
  it('shows help message', () => {
    const result = spawnSync(process.execPath, [scriptPath, '--help'], { encoding: 'utf8' });
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Usage:');
  });

  it('fails when uid is missing', () => {
    const result = spawnSync(process.execPath, [scriptPath], { encoding: 'utf8' });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('missing required --uid');
  });
});
