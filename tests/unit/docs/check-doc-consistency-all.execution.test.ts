import { basename } from 'node:path';

import { beforeAll, beforeEach, describe, expect, it, vi } from 'vitest';

const spawnSyncMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawnSync: (...args: unknown[]) => spawnSyncMock(...args),
}));

let main: (argv?: string[]) => number;

beforeAll(async () => {
  ({ main } = await import('../../../scripts/docs/check-doc-consistency-all.mjs'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
  spawnSyncMock.mockReturnValue({ status: 0 });
});

describe('check-doc-consistency-all execution order', () => {
  it('runs doc governance after contract catalog coverage', () => {
    const exitCode = main(['node', 'scripts/docs/check-doc-consistency-all.mjs']);

    expect(exitCode).toBe(0);
    const scriptNames = spawnSyncMock.mock.calls.map((call) => basename(String(call[1][0])));
    expect(scriptNames).toContain('check-contract-catalog-coverage.mjs');
    expect(scriptNames.at(-1)).toBe('check-doc-governance.mjs');
  });

  it('skips downstream governance checks for --docs filtered runs', () => {
    const exitCode = main([
      'node',
      'scripts/docs/check-doc-consistency-all.mjs',
      '--docs',
      'README.md,docs/README.md',
    ]);

    expect(exitCode).toBe(0);
    const scriptNames = spawnSyncMock.mock.calls.map((call) => basename(String(call[1][0])));
    expect(scriptNames).toEqual(['check-doc-consistency.mjs']);
  });
});
