import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';

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
});
