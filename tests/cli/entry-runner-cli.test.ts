import { describe, it, expect, beforeEach, beforeAll, vi } from 'vitest';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const spawnSyncMock = vi.fn();
const safeExitMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawnSync: (...args: unknown[]) => spawnSyncMock(...args),
}));

vi.mock('../../src/utils/safe-exit.js', () => ({
  safeExit: (...args: unknown[]) => safeExitMock(...args),
}));

let createEntryRunnerCommand: () => any;

beforeAll(async () => {
  ({ createEntryRunnerCommand } = await import('../../src/cli/entry-runner-cli.js'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
  safeExitMock.mockReset();
});

describe('entry runner CLI', () => {
  it('rejects unknown categories', async () => {
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    const command = createEntryRunnerCommand();

    await command.parseAsync(['node', 'cli', 'unknown']);

    expect(spawnSyncMock).not.toHaveBeenCalled();
    expect(safeExitMock).toHaveBeenCalledWith(2);
    consoleErrorSpy.mockRestore();
  });

  it('fails when runner entry is missing', async () => {
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    const tempRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'entry-runner-'));
    const command = createEntryRunnerCommand();

    await command.parseAsync(['node', 'cli', 'test', '--root', tempRoot]);

    expect(spawnSyncMock).not.toHaveBeenCalled();
    expect(safeExitMock).toHaveBeenCalledWith(2);
    consoleErrorSpy.mockRestore();
  });

  it('forwards args and uses root cwd', async () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const root = process.cwd();
    const runnerPath = path.join(root, 'scripts', 'test', 'run.mjs');

    spawnSyncMock.mockReturnValueOnce({ status: 0, error: null });

    const command = createEntryRunnerCommand();
    await command.parseAsync([
      'node',
      'cli',
      'test',
      '--root',
      root,
      '--profile',
      'fast',
      '--dry-run',
    ]);

    expect(spawnSyncMock).toHaveBeenCalledWith(
      process.execPath,
      [runnerPath, '--profile', 'fast', '--dry-run'],
      expect.objectContaining({
        cwd: root,
        stdio: 'inherit',
        env: process.env,
      })
    );
    expect(safeExitMock).toHaveBeenCalledWith(0);
    consoleLogSpy.mockRestore();
  });

  it('propagates non-zero exit codes', async () => {
    const root = process.cwd();
    const runnerPath = path.join(root, 'scripts', 'test', 'run.mjs');

    spawnSyncMock.mockReturnValueOnce({ status: 5, error: null });

    const command = createEntryRunnerCommand();
    await command.parseAsync(['node', 'cli', 'test', '--root', root, '--profile', 'fast']);

    expect(spawnSyncMock).toHaveBeenCalledWith(
      process.execPath,
      [runnerPath, '--profile', 'fast'],
      expect.objectContaining({
        cwd: root,
        stdio: 'inherit',
        env: process.env,
      })
    );
    expect(safeExitMock).toHaveBeenCalledWith(5);
  });
});
