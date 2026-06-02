import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';

const scriptPath = resolve('scripts/formal/verify-alloy.mjs');

function makeRepo() {
  const dir = mkdtempSync(join(tmpdir(), 'verify-alloy-security-'));
  mkdirSync(join(dir, 'spec', 'alloy'), { recursive: true });
  writeFileSync(join(dir, 'spec', 'alloy', 'Domain.als'), 'sig A {}\n', 'utf8');
  return dir;
}

describe('verify-alloy security behavior', () => {
  it('rejects unsafe Alloy file paths before tool execution', () => {
    const dir = makeRepo();
    const result = spawnSync(process.execPath, [scriptPath, '--file', '../outside.als'], {
      cwd: dir,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);
    const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'hermetic-reports', 'formal', 'alloy-summary.json'), 'utf8'));
    expect(summary.status).toBe('invalid_input');
    expect(summary.output).toContain('parent traversal');
  });

  it('does not execute ALLOY_RUN_CMD through a shell', () => {
    const dir = makeRepo();
    const marker = join(dir, 'shell-marker');
    const result = spawnSync(process.execPath, [scriptPath, '--file', 'spec/alloy/Domain.als'], {
      cwd: dir,
      encoding: 'utf8',
      env: {
        ...process.env,
        ALLOY_RUN_CMD: `node -e "require('fs').writeFileSync('${marker}', 'executed')"`,
      },
    });

    expect(result.status).toBe(0);
    expect(existsSync(marker)).toBe(false);
    const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'hermetic-reports', 'formal', 'alloy-summary.json'), 'utf8'));
    expect(summary.status).toBe('run_cmd_unsupported');
  });
});
