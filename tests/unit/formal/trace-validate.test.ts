import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/formal/trace-validate.mjs');

const runTraceValidate = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 30_000,
});

describe('trace-validate CLI', () => {
  it('validates the default selected trace when no path is provided', () => {
    const result = runTraceValidate([]);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('2 event(s) validated against trace schema');
  });

  it('accepts pnpm-style separator plus --in for project-local selected traces', () => {
    const result = runTraceValidate(['--', '--in', 'samples/conformance/sample-traces.json']);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('2 event(s) validated against trace schema');
  });

  it('rejects ambiguous positional paths when --in is already supplied', () => {
    const result = runTraceValidate([
      '--in',
      'samples/conformance/sample-traces.json',
      'samples/conformance/sample-traces.json',
    ]);

    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain('Unexpected extra trace file path');
  });
});
