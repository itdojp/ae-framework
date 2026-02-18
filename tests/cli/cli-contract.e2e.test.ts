import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';

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
  const start = stdout.indexOf('{');
  if (start < 0) {
    throw new Error(`JSON payload not found in stdout: ${stdout}`);
  }
  return JSON.parse(stdout.slice(start).trim());
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
        command: 'lint',
        input: 'spec/does-not-exist.json',
      }),
    );
    expect(typeof payload.ts).toBe('string');
  });
});
