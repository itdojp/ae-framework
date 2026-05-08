import { beforeEach, describe, expect, it, vi } from 'vitest';

const { execaMock } = vi.hoisted(() => ({
  execaMock: vi.fn(),
}));

vi.mock('execa', () => ({
  execa: execaMock,
}));

import { run } from '../../src/core/exec.js';

describe('core exec command boundary', () => {
  beforeEach(() => {
    execaMock.mockReset();
  });

  it('returns ok with normalized stdout for successful commands', async () => {
    execaMock.mockResolvedValueOnce({ exitCode: 0, stdout: new Uint8Array(Buffer.from('ok\n')) });

    const result = await run('unit-step', 'node', ['--version'], { cwd: process.cwd() });

    expect(execaMock).toHaveBeenCalledWith('node', ['--version'], expect.objectContaining({
      cwd: process.cwd(),
      reject: false,
    }));
    expect(result).toEqual({ ok: true, value: { stdout: 'ok\n' } });
  });

  it('returns E_EXEC for non-zero exits without throwing', async () => {
    execaMock.mockResolvedValueOnce({ exitCode: 2, stdout: 'bad input' });

    const result = await run('input-check', 'ae', ['bad']);

    expect(result).toEqual({
      ok: false,
      error: {
        code: 'E_EXEC',
        step: 'input-check',
        detail: 'exit 2',
      },
    });
  });

  it('returns E_EXEC with original message for spawn/internal errors', async () => {
    execaMock.mockRejectedValueOnce(new Error('spawn ENOENT'));

    const result = await run('internal-check', 'missing-bin', []);

    expect(result).toEqual({
      ok: false,
      error: {
        code: 'E_EXEC',
        step: 'internal-check',
        detail: 'spawn ENOENT',
      },
    });
  });
});
