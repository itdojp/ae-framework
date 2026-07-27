import { beforeEach, describe, expect, it, vi } from 'vitest';

const runMock = vi.hoisted(() => vi.fn());

vi.mock('../../../src/core/exec.js', () => ({
  run: runMock,
}));

import {
  chunkVitestFileArgs,
  qaFlake,
  VITEST_COMMAND_LINE_BUDGET,
} from '../../../src/commands/qa/flake.js';

describe('qaFlake Vitest selection', () => {
  beforeEach(() => {
    runMock.mockReset();
    runMock.mockResolvedValue({ ok: true, value: { exitCode: 0 } });
  });

  it('passes a concrete test path as a positional Vitest filter', async () => {
    const testPath = 'tests/unit/ci/nightly-workflow-reproducibility.test.ts';
    const result = await qaFlake({ times: 1, pattern: testPath, workers: 2 });

    expect(result.ok).toBe(true);
    expect(runMock).toHaveBeenCalledWith(
      'flake-run-1',
      'pnpm',
      ['test', testPath, '--maxWorkers', '2'],
      expect.objectContaining({ timeout: 300000, killSignal: 'SIGTERM' }),
    );
  });

  it('expands a glob to stable concrete file filters instead of using --dir', async () => {
    const result = await qaFlake({
      times: 1,
      pattern: 'tests/unit/formal/verify-*-semantics.test.ts',
      workers: '1',
    });

    expect(result.ok).toBe(true);
    const args = runMock.mock.calls[0]?.[2] as string[];
    expect(args).toContain('tests/unit/formal/verify-smt-semantics.test.ts');
    expect(args).toContain('tests/unit/formal/verify-spin-semantics.test.ts');
    expect(args).not.toContain('--dir');
    expect(args.slice(-2)).toEqual(['--maxWorkers', '1']);
  });

  it('chunks a large concrete selection below the Windows command-line budget', () => {
    const files = Array.from(
      { length: 1_000 },
      (_, index) => `tests/unit/generated/${String(index).padStart(4, '0')}-${'x'.repeat(32)}.test.ts`,
    );
    const fixedArgs = ['pnpm', 'test', '--maxWorkers', '2'];
    const batches = chunkVitestFileArgs(files, fixedArgs);

    expect(batches.length).toBeGreaterThan(1);
    expect(batches.flat()).toEqual(files);
    for (const batch of batches) {
      const estimatedLength = [...fixedArgs, ...batch]
        .reduce((total, value) => total + (value.length * 2) + 3, 0);
      expect(estimatedLength).toBeLessThanOrEqual(VITEST_COMMAND_LINE_BUDGET);
    }
  });

  it('runs the default broad selection in bounded batches without dropping matches', async () => {
    const result = await qaFlake({ times: 1, workers: 2 });

    expect(result.ok).toBe(true);
    expect(runMock.mock.calls.length).toBeGreaterThan(1);
    const selectedFiles = runMock.mock.calls.flatMap((call) =>
      (call[2] as string[]).filter((value) => value.startsWith('tests/')),
    );
    expect(selectedFiles.length).toBeGreaterThan(0);
    expect(new Set(selectedFiles).size).toBe(selectedFiles.length);
    for (const call of runMock.mock.calls) {
      const args = call[2] as string[];
      const estimatedLength = ['pnpm', ...args]
        .reduce((total, value) => total + (value.length * 2) + 3, 0);
      expect(estimatedLength).toBeLessThanOrEqual(VITEST_COMMAND_LINE_BUDGET);
    }
  });

  it('fails closed instead of forwarding an unmatched glob to Vitest', async () => {
    const result = await qaFlake({
      times: 1,
      pattern: 'tests/unit/missing/**/*.test.ts',
    });

    expect(result).toEqual({
      ok: false,
      error: {
        code: 'E_CONFIG',
        key: 'pattern',
        detail: 'glob pattern matched no test files: tests/unit/missing/**/*.test.ts',
      },
    });
    expect(runMock).not.toHaveBeenCalled();
  });

  it('normalizes a concrete fallback filter before forwarding it to Vitest', async () => {
    const result = await qaFlake({
      times: 1,
      pattern: 'tests\\unit\\missing.test.ts',
    });

    expect(result.ok).toBe(true);
    expect(runMock).toHaveBeenCalledWith(
      'flake-run-1',
      'pnpm',
      ['test', 'tests/unit/missing.test.ts'],
      expect.objectContaining({ timeout: 300000, killSignal: 'SIGTERM' }),
    );
  });
});
