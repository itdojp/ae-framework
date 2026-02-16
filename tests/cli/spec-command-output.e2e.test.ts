import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
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
  const start = stdout.indexOf('{');
  if (start < 0) {
    throw new Error(`JSON payload not found in stdout: ${stdout}`);
  }
  return JSON.parse(stdout.slice(start).trim());
};

describe('spec command output contracts', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = mkdtempSync(join(tmpdir(), 'ae-spec-cli-output-'));
  });

  afterEach(() => {
    rmSync(tempDir, { recursive: true, force: true });
  });

  it('emits lint report in JSON and writes to --output', () => {
    const irPath = join(tempDir, 'ae-ir.json');
    const lintReportPath = join(tempDir, 'lint-report.json');

    const compileResult = runCli(['spec', 'compile', '-i', 'spec/0_first_valid_spec.md', '-o', irPath]);
    expect(compileResult.status).toBe(0);

    const lintResult = runCli([
      'spec',
      'lint',
      '-i',
      irPath,
      '--format',
      'json',
      '--output',
      lintReportPath,
    ]);
    expect(lintResult.status).toBe(0);

    const stdoutReport = parseJsonFromStdout(lintResult.stdout);
    expect(stdoutReport.command).toBe('lint');
    expect(stdoutReport.summary).toEqual(
      expect.objectContaining({
        errors: expect.any(Number),
        warnings: expect.any(Number),
        info: expect.any(Number),
      }),
    );
    expect(Array.isArray(stdoutReport.issues)).toBe(true);
    expect(typeof stdoutReport.generatedAt).toBe('string');

    expect(existsSync(lintReportPath)).toBe(true);
    const outputReport = JSON.parse(readFileSync(lintReportPath, 'utf8'));
    expect(outputReport.command).toBe('lint');
  });

  it('keeps validate --output for AE-IR and writes JSON report with --report-output', () => {
    const irPath = join(tempDir, 'validated-ae-ir.json');
    const reportPath = join(tempDir, 'validate-report.json');

    const validateResult = runCli([
      'spec',
      'validate',
      '-i',
      'spec/0_first_valid_spec.md',
      '--output',
      irPath,
      '--format',
      'json',
      '--report-output',
      reportPath,
    ]);
    expect(validateResult.status).toBe(0);
    expect(existsSync(irPath)).toBe(true);
    expect(existsSync(reportPath)).toBe(true);

    const stdoutReport = parseJsonFromStdout(validateResult.stdout);
    expect(stdoutReport.command).toBe('validate');
    expect(stdoutReport.aeIrOutput).toBe(irPath);
    expect(stdoutReport.status).toBe('pass');

    const outputReport = JSON.parse(readFileSync(reportPath, 'utf8'));
    expect(outputReport.command).toBe('validate');
    expect(outputReport.aeIrOutput).toBe(irPath);
  });
});
