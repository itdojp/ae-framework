import { describe, expect, it, vi } from 'vitest';
import {
  EXIT_CODES,
  isExecutedAsMain,
  isSupportedNodeVersion,
  parseArgs,
  runBootstrapLocal,
} from '../../../scripts/project/bootstrap-local.mjs';

describe('bootstrap-local args', () => {
  it('parses options', () => {
    const options = parseArgs([
      'node',
      'bootstrap-local.mjs',
      '--skip-setup-hooks',
      '--skip-verify-lite',
      '--with-codex',
      '--json',
      '--output-dir',
      'reports/bootstrap',
    ]);

    expect(options.skipSetupHooks).toBe(true);
    expect(options.skipVerifyLite).toBe(true);
    expect(options.withCodex).toBe(true);
    expect(options.json).toBe(true);
    expect(options.outputDir).toBe('reports/bootstrap');
    expect(options.unknown).toEqual([]);
  });
});

describe('bootstrap-local prerequisites', () => {
  it('accepts supported Node.js range', () => {
    expect(isSupportedNodeVersion('v20.11.0')).toBe(true);
    expect(isSupportedNodeVersion('v22.3.0')).toBe(true);
  });

  it('rejects unsupported Node.js versions', () => {
    expect(isSupportedNodeVersion('v20.10.9')).toBe(false);
    expect(isSupportedNodeVersion('v23.0.0')).toBe(false);
    expect(isSupportedNodeVersion('v18.19.1')).toBe(false);
  });
});

describe('bootstrap-local module invocation guard', () => {
  it('returns false when argv path is missing', () => {
    expect(isExecutedAsMain(import.meta.url, undefined as unknown as string)).toBe(false);
  });
});

describe('bootstrap-local execution', () => {
  it('returns prerequisite error when checks fail', () => {
    const writeSummary = vi.fn(() => ({
      outputDir: '/tmp/out',
      jsonPath: '/tmp/out/bootstrap-summary.json',
      markdownPath: '/tmp/out/bootstrap-summary.md',
    }));

    const exitCode = runBootstrapLocal(
      {
        skipSetupHooks: false,
        skipVerifyLite: false,
        withCodex: false,
        skipCodex: false,
        json: false,
        outputDir: 'artifacts/bootstrap',
      },
      {
        checkPrerequisites: () => ({
          ok: false,
          issues: [{ code: 'pnpm_not_found', message: 'missing', fix: 'install pnpm' }],
        }),
        writeSummary,
      },
    );

    expect(exitCode).toBe(EXIT_CODES.PREREQUISITE_FAILED);
    expect(writeSummary).toHaveBeenCalledOnce();
  });

  it('returns command failure when required step fails', () => {
    const runCommand = vi
      .fn()
      .mockReturnValueOnce({ status: 0 })
      .mockReturnValueOnce({ status: 1 });
    const writeSummary = vi.fn(() => ({
      outputDir: '/tmp/out',
      jsonPath: '/tmp/out/bootstrap-summary.json',
      markdownPath: '/tmp/out/bootstrap-summary.md',
    }));

    const exitCode = runBootstrapLocal(
      {
        skipSetupHooks: false,
        skipVerifyLite: false,
        withCodex: true,
        skipCodex: false,
        json: false,
        outputDir: 'artifacts/bootstrap',
      },
      {
        checkPrerequisites: () => ({ ok: true, issues: [] }),
        runCommand,
        writeSummary,
      },
    );

    expect(exitCode).toBe(EXIT_CODES.COMMAND_FAILED);
    expect(runCommand).toHaveBeenCalledTimes(2);
  });

  it('succeeds and skips codex by default', () => {
    const runCommand = vi.fn().mockReturnValue({ status: 0 });
    const writeSummary = vi.fn(() => ({
      outputDir: '/tmp/out',
      jsonPath: '/tmp/out/bootstrap-summary.json',
      markdownPath: '/tmp/out/bootstrap-summary.md',
    }));

    const exitCode = runBootstrapLocal(
      {
        skipSetupHooks: false,
        skipVerifyLite: false,
        withCodex: false,
        skipCodex: false,
        json: false,
        outputDir: 'artifacts/bootstrap',
      },
      {
        checkPrerequisites: () => ({ ok: true, issues: [] }),
        runCommand,
        writeSummary,
      },
    );

    expect(exitCode).toBe(EXIT_CODES.SUCCESS);
    expect(runCommand).toHaveBeenCalledTimes(2);
  });
});
