import { describe, it, expect, beforeAll, beforeEach, vi } from 'vitest';
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

let createHelpCommand: () => any;

beforeAll(async () => {
  ({ createHelpCommand } = await import('../../src/cli/help-cli.js'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
  safeExitMock.mockReset();
});

describe('help CLI', () => {
  it('fails when help script is missing', async () => {
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    const tempRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'ae-help-'));
    const command = createHelpCommand();

    await command.parseAsync(['node', 'cli', '--root', tempRoot]);

    expect(spawnSyncMock).not.toHaveBeenCalled();
    expect(safeExitMock).toHaveBeenCalledWith(2);
    consoleErrorSpy.mockRestore();
  });

  it('runs help script from the provided root', async () => {
    const root = process.cwd();
    const scriptPath = path.join(root, 'scripts', 'project', 'help.mjs');

    spawnSyncMock.mockReturnValueOnce({ status: 0, error: null });

    const command = createHelpCommand();
    await command.parseAsync(['node', 'cli', '--root', root]);

    expect(spawnSyncMock).toHaveBeenCalledWith(
      process.execPath,
      [scriptPath],
      expect.objectContaining({
        cwd: root,
        stdio: 'inherit',
        env: process.env,
      })
    );
    expect(safeExitMock).toHaveBeenCalledWith(0);
  });

  it('returns 127 when the runner is missing', async () => {
    const root = process.cwd();
    spawnSyncMock.mockReturnValueOnce({
      status: null,
      error: Object.assign(new Error('not found'), { code: 'ENOENT' }),
    });

    const command = createHelpCommand();
    await command.parseAsync(['node', 'cli', '--root', root]);

    expect(safeExitMock).toHaveBeenCalledWith(127);
  });

  it('propagates non-zero exit codes', async () => {
    const root = process.cwd();
    spawnSyncMock.mockReturnValueOnce({ status: 7, error: null });

    const command = createHelpCommand();
    await command.parseAsync(['node', 'cli', '--root', root]);

    expect(safeExitMock).toHaveBeenCalledWith(7);
  });

  it('returns 1 for spawn errors without ENOENT', async () => {
    const root = process.cwd();
    spawnSyncMock.mockReturnValueOnce({
      status: null,
      error: Object.assign(new Error('spawn failed'), { code: 'EACCES' }),
    });

    const command = createHelpCommand();
    await command.parseAsync(['node', 'cli', '--root', root]);

    expect(safeExitMock).toHaveBeenCalledWith(1);
  });
});
