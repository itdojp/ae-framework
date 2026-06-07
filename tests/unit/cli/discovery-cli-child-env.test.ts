import { beforeAll, beforeEach, describe, expect, it, vi } from 'vitest';

const spawnSyncMock = vi.fn();
const safeExitMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawnSync: (...args: unknown[]) => spawnSyncMock(...args),
}));

vi.mock('../../../src/utils/safe-exit.js', () => ({
  safeExit: (...args: unknown[]) => safeExitMock(...args),
}));

let createDiscoveryCommand: () => any;

beforeAll(async () => {
  ({ createDiscoveryCommand } = await import('../../../src/cli/discovery-cli.js'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
  safeExitMock.mockReset();
});

describe('discovery CLI child process environment', () => {
  it('does not forward ambient GitHub tokens to discovery scripts', async () => {
    const previousToken = process.env['GITHUB_TOKEN'];
    process.env['GITHUB_TOKEN'] = 'raw-discovery-token';
    spawnSyncMock.mockReturnValueOnce({ status: 0, error: null });

    let childEnvSnapshot: NodeJS.ProcessEnv = {};
    try {
      const command = createDiscoveryCommand();
      await command.parseAsync([
        'node',
        'cli',
        'validate',
        '--format',
        'json',
        '--sources',
        'docs/**/*.md',
      ]);
      const spawnOptions = spawnSyncMock.mock.calls[0]?.[2] as { env?: NodeJS.ProcessEnv } | undefined;
      childEnvSnapshot = { ...(spawnOptions?.env ?? {}) };
    } finally {
      if (previousToken === undefined) {
        delete process.env['GITHUB_TOKEN'];
      } else {
        process.env['GITHUB_TOKEN'] = previousToken;
      }
    }

    expect(childEnvSnapshot).not.toHaveProperty('GITHUB_TOKEN');
    expect(spawnSyncMock).toHaveBeenCalledWith(
      process.execPath,
      expect.arrayContaining(['--format', 'json', '--sources', 'docs/**/*.md']),
      expect.objectContaining({
        cwd: process.cwd(),
        encoding: 'utf8',
        env: expect.any(Object),
      }),
    );
    expect(safeExitMock).toHaveBeenCalledWith(0);
  });
});
