import { describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';

const tlaScriptPath = resolve('scripts/formal/verify-tla.mjs');
const apalacheScriptPath = resolve('scripts/formal/verify-apalache.mjs');

function makeRepo() {
  const dir = mkdtempSync(join(tmpdir(), 'verify-tla-input-security-'));
  mkdirSync(join(dir, 'spec', 'tla'), { recursive: true });
  writeFileSync(join(dir, 'spec', 'tla', 'DomainSpec.tla'), '---- MODULE DomainSpec ----\n====\n', 'utf8');
  return dir;
}

describe('formal TLA input security', () => {
  it('verify-tla rejects traversal paths before external tool execution', () => {
    const dir = makeRepo();
    const result = spawnSync(process.execPath, [tlaScriptPath, '--engine=tlc', '--file', '../package.json'], {
      cwd: dir,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);
    const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'hermetic-reports', 'formal', 'tla-summary.json'), 'utf8'));
    expect(summary.status).toBe('invalid_input');
    expect(summary.output).toContain('parent traversal');
  });

  it('verify-apalache rejects paths outside spec/tla before external tool execution', () => {
    const dir = makeRepo();
    mkdirSync(join(dir, 'spec', 'alloy'), { recursive: true });
    writeFileSync(join(dir, 'spec', 'alloy', 'Domain.als'), 'sig A {}\n', 'utf8');

    const result = spawnSync(process.execPath, [apalacheScriptPath, '--file', 'spec/alloy/Domain.als'], {
      cwd: dir,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);
    const summary = JSON.parse(readFileSync(join(dir, 'artifacts', 'hermetic-reports', 'formal', 'apalache-summary.json'), 'utf8'));
    expect(summary.status).toBe('invalid_input');
    expect(summary.output).toContain('Apalache TLA file must use one of these extensions');
  });
});
