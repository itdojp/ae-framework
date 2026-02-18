import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const tsxBin = resolve('node_modules/.bin/tsx');

const runCli = (args: string[]) =>
  spawnSync(tsxBin, ['src/cli/index.ts', ...args], {
    encoding: 'utf8',
    timeout: 60_000,
    env: {
      ...process.env,
      VITEST: '',
      NODE_ENV: 'production',
      AE_TEST_NO_EXIT: '0',
    },
  });

const parseJsonFromStdout = (stdout: string) => {
  let start = stdout.indexOf('{');
  while (start >= 0) {
    const candidate = stdout.slice(start).trim();
    try {
      return JSON.parse(candidate);
    } catch {
      start = stdout.indexOf('{', start + 1);
    }
  }
  throw new Error(`JSON payload not found in stdout: ${stdout}`);
};

describe('CLI contract (help / invalid input / json error)', () => {
  it('returns exit code 0 for --help', () => {
    const result = runCli(['--help']);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Usage:');
  });

  it('returns exit code 2 for unknown command', () => {
    const result = runCli(['unknown-subcommand']);
    expect(result.status).toBe(2);
    expect(result.stderr).toContain("unknown command 'unknown-subcommand'");
  });

  it('emits parseable error JSON when --format json and input is invalid', () => {
    const result = runCli([
      'spec',
      'lint',
      '--input',
      'spec/does-not-exist.json',
      '--format',
      'json',
    ]);

    expect(result.status).toBe(2);
    const payload = parseJsonFromStdout(result.stdout);
    expect(payload).toEqual(
      expect.objectContaining({
        error: true,
        code: 'SPEC_INVALID_INPUT',
        command: 'lint',
      }),
    );
    expect(payload.details).toEqual(
      expect.objectContaining({
        input: 'spec/does-not-exist.json',
      }),
    );
    expect(typeof payload.ts).toBe('string');
  });

  it('classifies malformed JSON input as invalid input', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-cli-contract-'));
    try {
      const malformedPath = join(dir, 'malformed.json');
      writeFileSync(malformedPath, '{ invalid json', 'utf8');
      const result = runCli([
        'spec',
        'lint',
        '--input',
        malformedPath,
        '--format',
        'json',
      ]);
      expect(result.status).toBe(2);
      const payload = parseJsonFromStdout(result.stdout);
      expect(payload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'SPEC_INVALID_INPUT',
          command: 'lint',
        }),
      );
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('emits parseable error JSON when an unknown --format is provided', () => {
    const result = runCli([
      'spec',
      'lint',
      '--input',
      'spec/does-not-exist.json',
      '--format',
      'xml',
    ]);

    expect(result.status).toBe(2);
    const payload = parseJsonFromStdout(result.stdout);
    expect(payload).toEqual(
      expect.objectContaining({
        error: true,
        code: 'SPEC_INVALID_INPUT',
        command: 'lint',
      }),
    );
  });
});
