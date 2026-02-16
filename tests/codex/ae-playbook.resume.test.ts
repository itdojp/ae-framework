import { describe, it, expect } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';

const scriptPath = resolve('scripts/codex/ae-playbook.mjs');
const skipAllPhases = '--skip=setup,qa,spec,sim,formal,coverage,adapters';

const runPlaybook = (cwd: string) => {
  return spawnSync(process.execPath, [scriptPath, '--resume', skipAllPhases], {
    cwd,
    encoding: 'utf8',
    timeout: 60_000,
  });
};

describe('ae-playbook --resume context compatibility', () => {
  it('migrates context.json without phases', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-playbook-resume-'));
    const artifactsDir = join(dir, 'artifacts', 'ae');
    mkdirSync(artifactsDir, { recursive: true });
    writeFileSync(join(artifactsDir, 'context.json'), JSON.stringify({ runId: 'legacy' }, null, 2));

    const result = runPlaybook(dir);
    expect(result.status).toBe(0);

    const updated = JSON.parse(readFileSync(join(artifactsDir, 'context.json'), 'utf8'));
    expect(updated.phases).toBeDefined();
    expect(typeof updated.phases).toBe('object');
    expect(updated.phases.setup?.skipped).toBe(true);

    rmSync(dir, { recursive: true, force: true });
  });

  it('returns validation error for invalid context JSON', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-playbook-invalid-'));
    const artifactsDir = join(dir, 'artifacts', 'ae');
    mkdirSync(artifactsDir, { recursive: true });
    writeFileSync(join(artifactsDir, 'context.json'), '{ invalid-json');

    const result = runPlaybook(dir);
    expect(result.status).toBe(2);
    expect(result.stderr).toContain('context.json is invalid JSON');

    rmSync(dir, { recursive: true, force: true });
  });
});
