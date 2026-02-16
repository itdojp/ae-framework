import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { resolve } from 'node:path';
import { join } from 'node:path';

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

describe('validate command routing', () => {
  it('routes --traceability even when argv starts with standalone --', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-validate-trace-'));
    const file = join(dir, 'traceability.md');
    writeFileSync(
      file,
      [
        'REQ-1 links to US-1 and SPEC-1',
        'REQ-2 links to US-2 and SPEC-2',
      ].join('\n'),
      'utf8',
    );
    const result = runCli(['--', 'validate', '--traceability', '--sources', file]);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Traceability Validation Complete');
    expect(result.stdout).toContain('Requested: 1');
    expect(result.stdout).toContain('Resolved:');
    rmSync(dir, { recursive: true, force: true });
  });

  it('routes --stories to user stories validation', () => {
    const result = runCli(['validate', '--stories', '--sources', 'spec/0_first_valid_spec.md']);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('User Stories Validation Complete');
  });

  it('routes --specifications to specification validation', () => {
    const result = runCli(['validate', '--specifications', '--sources', 'spec/0_first_valid_spec.md']);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Specification Validation Complete');
  });

  it('routes --completeness to completeness validation', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-validate-complete-'));
    const file = join(dir, 'completeness.md');
    writeFileSync(
      file,
      [
        'Requirement: The service must authenticate users.',
        'As a user, I want secure login so that my data is protected.',
        'Specification: API schema includes auth endpoint and response model.',
        'Test scenario: Given valid credentials, When login is requested, Then token is issued.',
      ].join('\n'),
      'utf8',
    );
    const result = runCli(['validate', '--completeness', '--sources', file]);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Completeness Validation Complete');
    rmSync(dir, { recursive: true, force: true });
  });

  it('returns non-zero for unresolved --sources', () => {
    const result = runCli(['validate', '--traceability', '--sources', 'nonexistent-path-2014']);
    expect(result.status).toBe(1);
    expect(result.stdout).toContain('No readable validation sources found');
  });

  it('treats whitespace file paths as filesystem sources when the file exists', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-validate-space-'));
    const file = join(dir, 'spec v2.md');
    writeFileSync(
      file,
      [
        'REQ-SPACE-1 must be traceable to STORY-SPACE-1 and SPEC-SPACE-1',
        'REQ-SPACE-2 must be traceable to STORY-SPACE-2 and SPEC-SPACE-2',
      ].join('\n'),
      'utf8',
    );

    const result = runCli(['validate', '--traceability', '--sources', file]);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Traceability Validation Complete');
    expect(result.stdout).toContain('Resolved: 1');
    expect(result.stdout).not.toContain('inline:');

    rmSync(dir, { recursive: true, force: true });
  });
});
