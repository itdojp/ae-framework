import { describe, expect, it, vi } from 'vitest';
import {
  EXIT_CODES,
  isExecutedAsMain,
  main,
  parseArgs,
  runFirstRun,
  shellEscape,
} from '../../../scripts/onboarding/first-run.mjs';

describe('first-run module invocation guard', () => {
  it('returns false when argv path is missing', () => {
    expect(isExecutedAsMain(import.meta.url, undefined as unknown as string)).toBe(false);
  });
});

describe('first-run execution', () => {
  it('parses known options', () => {
    const options = parseArgs([
      'node',
      'first-run.mjs',
      '--json',
      '--output-dir',
      'reports/first-run',
      '--help',
    ]);
    expect(options.json).toBe(true);
    expect(options.outputDir).toBe('reports/first-run');
    expect(options.help).toBe(true);
    expect(options.unknown).toEqual([]);
  });

  it('escapes single quotes for single-quoted shell usage', () => {
    const escaped = shellEscape("foo'bar");
    expect(escaped).toBe("'foo'\\''bar'");
  });

  it('returns invalid-argument exit code for unknown options', () => {
    const code = main(['node', 'first-run.mjs', '--unknown-flag']);
    expect(code).toBe(EXIT_CODES.INVALID_ARGUMENT);
  });

  it('returns success when all required steps pass', () => {
    const executeStep = vi
      .fn()
      .mockReturnValueOnce({
        id: 'doctor',
        label: 'doctor:env',
        command: 'pnpm run doctor:env',
        required: true,
        status: 'passed',
        exitCode: 0,
        durationMs: 10,
        logPath: '/tmp/doctor.log',
      })
      .mockReturnValueOnce({
        id: 'build',
        label: 'build',
        command: 'pnpm run build',
        required: true,
        status: 'passed',
        exitCode: 0,
        durationMs: 20,
        logPath: '/tmp/build.log',
      })
      .mockReturnValueOnce({
        id: 'verifyLite',
        label: 'verify:lite',
        command: 'pnpm run verify:lite',
        required: true,
        status: 'passed',
        exitCode: 0,
        durationMs: 30,
        logPath: '/tmp/verify.log',
      });

    const writeSummary = vi.fn((summary) => ({
      outputDir: '/tmp/out',
      jsonPath: '/tmp/out/summary.json',
      markdownPath: '/tmp/out/summary.md',
      summary,
    }));

    const exitCode = runFirstRun(
      { outputDir: 'artifacts/first-run', json: false, help: false, unknown: [] },
      {
        cwd: '/tmp/repo',
        nowIso: () => '2026-02-17T00:00:00.000Z',
        executeStep,
        writeSummary,
      },
    );

    expect(exitCode).toBe(EXIT_CODES.SUCCESS);
    expect(executeStep).toHaveBeenCalledTimes(3);
    expect(writeSummary).toHaveBeenCalledOnce();
    const summary = writeSummary.mock.calls[0]?.[0];
    expect(summary.nextActions[0]).toContain('setup-hooks');
  });

  it('stops after first required failure and returns failed exit code', () => {
    const executeStep = vi
      .fn()
      .mockReturnValueOnce({
        id: 'doctor',
        label: 'doctor:env',
        command: 'pnpm run doctor:env',
        required: true,
        status: 'failed',
        exitCode: 1,
        durationMs: 10,
        logPath: '/tmp/doctor.log',
      });

    const writeSummary = vi.fn(() => ({
      outputDir: '/tmp/out',
      jsonPath: '/tmp/out/summary.json',
      markdownPath: '/tmp/out/summary.md',
    }));

    const exitCode = runFirstRun(
      { outputDir: 'artifacts/first-run', json: false, help: false, unknown: [] },
      {
        cwd: '/tmp/repo',
        nowIso: () => '2026-02-17T00:00:00.000Z',
        executeStep,
        writeSummary,
      },
    );

    expect(exitCode).toBe(EXIT_CODES.FAILED);
    expect(executeStep).toHaveBeenCalledTimes(1);
    expect(writeSummary).toHaveBeenCalledOnce();
    const summary = writeSummary.mock.calls[0]?.[0];
    expect(summary.nextActions[0]).toContain('artifacts/doctor/env.json');
  });

  it('continues when doctor exits with warning code 2', () => {
    const executeStep = vi
      .fn()
      .mockReturnValueOnce({
        id: 'doctor',
        label: 'doctor:env',
        command: 'pnpm run doctor:env',
        required: true,
        status: 'failed',
        exitCode: 2,
        durationMs: 10,
        logPath: '/tmp/doctor.log',
      })
      .mockReturnValueOnce({
        id: 'build',
        label: 'build',
        command: 'pnpm run build',
        required: true,
        status: 'passed',
        exitCode: 0,
        durationMs: 20,
        logPath: '/tmp/build.log',
      })
      .mockReturnValueOnce({
        id: 'verifyLite',
        label: 'verify:lite',
        command: 'pnpm run verify:lite',
        required: true,
        status: 'passed',
        exitCode: 0,
        durationMs: 30,
        logPath: '/tmp/verify.log',
      });
    const writeSummary = vi.fn(() => ({
      outputDir: '/tmp/out',
      jsonPath: '/tmp/out/summary.json',
      markdownPath: '/tmp/out/summary.md',
    }));

    const exitCode = runFirstRun(
      { outputDir: 'artifacts/first-run', json: false, help: false, unknown: [] },
      {
        cwd: '/tmp/repo',
        nowIso: () => '2026-02-17T00:00:00.000Z',
        executeStep,
        writeSummary,
      },
    );

    expect(exitCode).toBe(EXIT_CODES.SUCCESS);
    expect(executeStep).toHaveBeenCalledTimes(3);
    const summary = writeSummary.mock.calls[0]?.[0];
    expect(summary.steps[0]?.status).toBe('warn');
  });

  it('normalizes first-run summary artifact path for absolute output-dir', () => {
    const executeStep = vi.fn().mockReturnValue({
      id: 'doctor',
      label: 'doctor:env',
      command: 'pnpm run doctor:env',
      required: true,
      status: 'passed',
      exitCode: 0,
      durationMs: 10,
      logPath: '/tmp/doctor.log',
    });
    const writeSummary = vi.fn(() => ({
      outputDir: '/tmp/out',
      jsonPath: '/tmp/out/summary.json',
      markdownPath: '/tmp/out/summary.md',
    }));

    runFirstRun(
      { outputDir: '/tmp/abs/first-run', json: false, help: false, unknown: [] },
      {
        cwd: '/tmp/repo',
        executeStep,
        writeSummary,
      },
    );

    const summary = writeSummary.mock.calls[0]?.[0];
    expect(summary.keyArtifacts[2]?.path).not.toMatch(/^\/tmp\/abs/);
  });

  it('returns internal error when summary write fails', () => {
    const executeStep = vi.fn().mockReturnValue({
      id: 'doctor',
      label: 'doctor:env',
      command: 'pnpm run doctor:env',
      required: true,
      status: 'passed',
      exitCode: 0,
      durationMs: 10,
      logPath: '/tmp/doctor.log',
    });

    const exitCode = runFirstRun(
      { outputDir: 'artifacts/first-run', json: false, help: false, unknown: [] },
      {
        cwd: '/tmp/repo',
        executeStep,
        writeSummary: () => {
          throw new Error('disk full');
        },
      },
    );

    expect(exitCode).toBe(EXIT_CODES.INTERNAL_ERROR);
  });
});
