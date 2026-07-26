import { beforeEach, describe, expect, it, vi } from 'vitest';

const runMock = vi.hoisted(() => vi.fn());

vi.mock('../../../src/core/exec.js', () => ({
  run: runMock,
}));

import { qaFlake } from '../../../src/commands/qa/flake.js';

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
