import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import Ajv from 'ajv';
import addFormats from 'ajv-formats';

const repoRoot = resolve('.');
const tsxBin = resolve('node_modules/.bin/tsx');
const nodeBin = process.execPath;

const specReportSchema = JSON.parse(readFileSync(resolve('schema/spec-validation-report.schema.json'), 'utf8'));
const verifyProfileSchema = JSON.parse(readFileSync(resolve('schema/verify-profile-summary.schema.json'), 'utf8'));
const qualityReportSchema = JSON.parse(readFileSync(resolve('schema/quality-report.schema.json'), 'utf8'));

const runAeCli = (args: string[]) =>
  spawnSync(tsxBin, ['src/cli/index.ts', ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
    env: {
      ...process.env,
      VITEST: '',
      NODE_ENV: 'production',
      AE_TEST_NO_EXIT: '0',
    },
  });

const runVerifyProfile = (args: string[]) =>
  spawnSync(nodeBin, ['scripts/verify/run.mjs', ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
    env: {
      ...process.env,
      VITEST: '',
      NODE_ENV: 'production',
    },
  });

const parseJsonFromStdout = (stdout: string) => {
  let start = stdout.indexOf('{');
  while (start >= 0) {
    const candidate = stdout.slice(start).trim();
    try {
      return JSON.parse(candidate) as Record<string, unknown>;
    } catch {
      start = stdout.indexOf('{', start + 1);
    }
  }
  throw new Error(`JSON payload not found in stdout: ${stdout}`);
};

describe('CLI/Artifacts contract conformance', () => {
  it('spec lint --format json follows schema and exit code contract (success/input)', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-contract-spec-lint-'));
    try {
      const irPath = join(tempDir, 'ae-ir.json');
      const lintReportPath = join(tempDir, 'artifacts', 'spec', 'lint-report.json');

      const compileResult = runAeCli([
        'spec',
        'compile',
        '-i',
        'spec/0_first_valid_spec.md',
        '-o',
        irPath,
      ]);
      expect(compileResult.status).toBe(0);

      const lintResult = runAeCli([
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

      const ajv = new Ajv2020({ allErrors: true, strict: false });
      addFormats(ajv);
      const validate = ajv.compile(specReportSchema);

      const stdoutPayload = parseJsonFromStdout(lintResult.stdout);
      expect(validate(stdoutPayload), JSON.stringify(validate.errors)).toBe(true);
      expect(existsSync(lintReportPath)).toBe(true);

      const reportPayload = JSON.parse(readFileSync(lintReportPath, 'utf8')) as Record<string, unknown>;
      expect(validate(reportPayload), JSON.stringify(validate.errors)).toBe(true);

      const invalidInputResult = runAeCli([
        'spec',
        'lint',
        '-i',
        join(tempDir, 'missing.json'),
        '--format',
        'json',
      ]);
      expect(invalidInputResult.status).toBe(2);
      const invalidPayload = parseJsonFromStdout(invalidInputResult.stdout);
      expect(invalidPayload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'SPEC_INVALID_INPUT',
          command: 'lint',
        }),
      );
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('spec validate --format json follows schema and exit code contract (success/input/internal)', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-contract-spec-validate-'));
    try {
      const irPath = join(tempDir, 'ae-ir.json');
      const validateReportPath = join(tempDir, 'artifacts', 'spec', 'validate-report.json');

      const validateResult = runAeCli([
        'spec',
        'validate',
        '-i',
        'spec/0_first_valid_spec.md',
        '--output',
        irPath,
        '--format',
        'json',
        '--report-output',
        validateReportPath,
      ]);
      expect(validateResult.status).toBe(0);
      expect(existsSync(irPath)).toBe(true);
      expect(existsSync(validateReportPath)).toBe(true);

      const ajv = new Ajv2020({ allErrors: true, strict: false });
      addFormats(ajv);
      const validateSchema = ajv.compile(specReportSchema);
      const stdoutPayload = parseJsonFromStdout(validateResult.stdout);
      expect(validateSchema(stdoutPayload), JSON.stringify(validateSchema.errors)).toBe(true);

      const invalidInputResult = runAeCli([
        'spec',
        'validate',
        '-i',
        join(tempDir, 'missing-spec.md'),
        '--format',
        'json',
      ]);
      expect(invalidInputResult.status).toBe(2);
      const invalidPayload = parseJsonFromStdout(invalidInputResult.stdout);
      expect(invalidPayload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'SPEC_INVALID_INPUT',
          command: 'validate',
        }),
      );

      const notDirectoryPath = join(tempDir, 'not-a-dir');
      writeFileSync(notDirectoryPath, 'x', 'utf8');
      const internalErrorResult = runAeCli([
        'spec',
        'validate',
        '-i',
        'spec/0_first_valid_spec.md',
        '--output',
        join(tempDir, 'internal-ae-ir.json'),
        '--format',
        'json',
        '--report-output',
        join(notDirectoryPath, 'report.json'),
      ]);
      expect(internalErrorResult.status).toBe(1);
      const internalPayload = parseJsonFromStdout(internalErrorResult.stdout);
      expect(internalPayload).toEqual(
        expect.objectContaining({
          error: true,
          code: 'SPEC_INTERNAL_ERROR',
          command: 'validate',
        }),
      );
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('verify:profile --json follows schema and exit code contract (success/input/internal)', () => {
    const tempDir = mkdtempSync(join(tmpdir(), 'ae-contract-verify-profile-'));
    try {
      const summaryPath = join(tempDir, 'artifacts', 'verify-profile-summary.json');
      const successResult = runVerifyProfile([
        '--profile',
        'fast',
        '--dry-run',
        '--json',
        '--out',
        summaryPath,
      ]);

      expect(successResult.status).toBe(0);
      expect(existsSync(summaryPath)).toBe(true);

      const ajv = new Ajv({ allErrors: true, strict: false });
      addFormats(ajv);
      const validate = ajv.compile(verifyProfileSchema);
      const stdoutPayload = parseJsonFromStdout(successResult.stdout);
      expect(validate(stdoutPayload), JSON.stringify(validate.errors)).toBe(true);

      const filePayload = JSON.parse(readFileSync(summaryPath, 'utf8')) as Record<string, unknown>;
      expect(validate(filePayload), JSON.stringify(validate.errors)).toBe(true);

      const unknownProfileResult = runVerifyProfile([
        '--profile',
        'unknown',
        '--json',
      ]);
      expect(unknownProfileResult.status).toBe(2);

      const missingProfileResult = runVerifyProfile(['--json']);
      expect(missingProfileResult.status).toBe(3);

      const outDir = join(tempDir, 'existing-directory');
      mkdirSync(outDir);
      const writeFailureResult = runVerifyProfile([
        '--profile',
        'fast',
        '--dry-run',
        '--json',
        '--out',
        outDir,
      ]);
      expect(writeFailureResult.status).toBe(1);
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('quality run --format json follows output/exit contract (success/input)', () => {
    const successResult = runAeCli([
      'quality',
      'run',
      '--format',
      'json',
      '--dry-run',
      '--gates',
      'linting',
    ]);
    expect(successResult.status).toBe(0);
    const payload = parseJsonFromStdout(successResult.stdout);
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(qualityReportSchema);
    expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);

    const invalidFormatResult = runAeCli([
      'quality',
      'run',
      '--format',
      'xml',
      '--dry-run',
    ]);
    expect(invalidFormatResult.status).toBe(2);
  });

  it('quality reconcile --format json follows output contract (success)', () => {
    const result = runAeCli([
      'quality',
      'reconcile',
      '--format',
      'json',
      '--dry-run',
      '--max-rounds',
      '1',
      '--gates',
      'linting',
    ]);
    expect(result.status).toBe(0);
    const payload = parseJsonFromStdout(result.stdout);
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(qualityReportSchema);
    expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
  });
});
