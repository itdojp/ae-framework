import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';

const tsxBin = resolve('node_modules/.bin/tsx');

const runCli = (args: string[]) => {
  const env = {
    ...process.env,
    VITEST: '',
    NODE_ENV: 'production',
    AE_TEST_NO_EXIT: '0',
  };
  return spawnSync(tsxBin, ['src/cli/index.ts', ...args], {
    encoding: 'utf8',
    timeout: 60_000,
    env,
  });
};

describe('intent analyze --sources', () => {
  it('does not crash with toLowerCase undefined', () => {
    const result = runCli(['intent', '--analyze', '--sources', 'spec/0_first_valid_spec.md']);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Intent analysis completed');
    expect(`${result.stdout}\n${result.stderr}`).not.toContain("toLowerCase");
  });

  it('returns diagnostic for unresolved sources', () => {
    const result = runCli(['intent', '--analyze', '--sources', 'missing-intent-source']);
    expect(result.status).toBe(1);
    expect(`${result.stdout}\n${result.stderr}`).toContain('Intent sources could not be resolved: missing-intent-source');
  });
});
