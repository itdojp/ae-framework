import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { spawnSync } from 'node:child_process';

// Mock child_process module
vi.mock('node:child_process', () => ({
  spawnSync: vi.fn(),
}));

// Import after mocking to ensure the mock is applied
const mockSpawnSync = spawnSync as ReturnType<typeof vi.fn>;

// Helper functions from verify-apalache.mjs
// We extract these for testing purposes
function commandExists(cmd: string): boolean {
  const result = mockSpawnSync(cmd, [], { stdio: 'ignore' });
  if (result.error && (result.error as NodeJS.ErrnoException).code === 'ENOENT') {
    return false;
  }
  return true;
}

function runCommand(cmd: string, cmdArgs: string[]): {
  available: boolean;
  success: boolean;
  status: number | null;
  signal: string | null;
  output: string;
} {
  const result = mockSpawnSync(cmd, cmdArgs, { encoding: 'utf8' });
  if (result.error) {
    if ((result.error as NodeJS.ErrnoException).code === 'ENOENT') {
      return { available: false, success: false, status: null, signal: null, output: '' };
    }
    return {
      available: true,
      success: false,
      status: result.status ?? null,
      signal: result.signal ?? null,
      output: result.error.message ?? '',
    };
  }
  const stdout = result.stdout ?? '';
  const stderr = result.stderr ?? '';
  return {
    available: true,
    success: result.status === 0,
    status: result.status ?? null,
    signal: result.signal ?? null,
    output: `${stdout}${stderr}`,
  };
}

function resolveCommandPath(cmd: string): string {
  if (!commandExists('which')) return '';
  const result = runCommand('which', [cmd]);
  if (!result.available || !result.success) return '';
  return result.output.trim().split(/\r?\n/)[0] || '';
}

describe('verify-apalache helper functions', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('commandExists', () => {
    it('returns true when command exists', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: 0,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 1234,
        output: ['', '', ''],
      } as any);

      expect(commandExists('apalache')).toBe(true);
      expect(mockSpawnSync).toHaveBeenCalledWith('apalache', [], { stdio: 'ignore' });
    });

    it('returns false when command does not exist (ENOENT)', () => {
      const enoentError = new Error('Command not found') as NodeJS.ErrnoException;
      enoentError.code = 'ENOENT';
      mockSpawnSync.mockReturnValue({
        error: enoentError,
        status: null,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 0,
        output: ['', '', ''],
      } as any);

      expect(commandExists('nonexistent')).toBe(false);
      expect(mockSpawnSync).toHaveBeenCalledWith('nonexistent', [], { stdio: 'ignore' });
    });

    it('returns true when command exists but returns non-zero exit code', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: 1,
        signal: null,
        stdout: '',
        stderr: 'Some error',
        pid: 1234,
        output: ['', '', ''],
      } as any);

      expect(commandExists('failing-command')).toBe(true);
    });

    it('returns true when command is killed by signal', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: null,
        signal: 'SIGTERM',
        stdout: '',
        stderr: '',
        pid: 1234,
        output: ['', '', ''],
      } as any);

      expect(commandExists('killed-command')).toBe(true);
    });
  });

  describe('runCommand', () => {
    it('returns success result when command succeeds', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: 0,
        signal: null,
        stdout: 'Success output',
        stderr: '',
        pid: 1234,
        output: ['', 'Success output', ''],
      } as any);

      const result = runCommand('apalache', ['version']);
      expect(result).toEqual({
        available: true,
        success: true,
        status: 0,
        signal: null,
        output: 'Success output',
      });
      expect(mockSpawnSync).toHaveBeenCalledWith('apalache', ['version'], { encoding: 'utf8' });
    });

    it('returns failure with ENOENT when command not found', () => {
      const enoentError = new Error('Command not found') as NodeJS.ErrnoException;
      enoentError.code = 'ENOENT';
      mockSpawnSync.mockReturnValue({
        error: enoentError,
        status: null,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 0,
        output: ['', '', ''],
      } as any);

      const result = runCommand('nonexistent', ['arg']);
      expect(result).toEqual({
        available: false,
        success: false,
        status: null,
        signal: null,
        output: '',
      });
    });

    it('returns failure when command exits with non-zero status', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: 1,
        signal: null,
        stdout: '',
        stderr: 'Error message',
        pid: 1234,
        output: ['', '', 'Error message'],
      } as any);

      const result = runCommand('apalache', ['check', 'invalid.tla']);
      expect(result).toEqual({
        available: true,
        success: false,
        status: 1,
        signal: null,
        output: 'Error message',
      });
    });

    it('combines stdout and stderr in output', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: 0,
        signal: null,
        stdout: 'stdout content\n',
        stderr: 'stderr content\n',
        pid: 1234,
        output: ['', 'stdout content\n', 'stderr content\n'],
      } as any);

      const result = runCommand('test', ['arg']);
      expect(result.output).toBe('stdout content\nstderr content\n');
    });

    it('handles command killed by signal', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: null,
        signal: 'SIGTERM',
        stdout: 'Partial output',
        stderr: '',
        pid: 1234,
        output: ['', 'Partial output', ''],
      } as any);

      const result = runCommand('long-running', []);
      expect(result).toEqual({
        available: true,
        success: false,
        status: null,
        signal: 'SIGTERM',
        output: 'Partial output',
      });
    });

    it('handles error with message when not ENOENT', () => {
      const permError = new Error('Permission denied') as NodeJS.ErrnoException;
      permError.code = 'EACCES';
      mockSpawnSync.mockReturnValue({
        error: permError,
        status: null,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 0,
        output: ['', '', ''],
      } as any);

      const result = runCommand('restricted', []);
      expect(result).toEqual({
        available: true,
        success: false,
        status: null,
        signal: null,
        output: 'Permission denied',
      });
    });
  });

  describe('resolveCommandPath', () => {
    it('returns empty string when which command does not exist', () => {
      // First call for commandExists('which')
      const enoentError = new Error('Command not found') as NodeJS.ErrnoException;
      enoentError.code = 'ENOENT';
      mockSpawnSync.mockReturnValueOnce({
        error: enoentError,
        status: null,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 0,
        output: ['', '', ''],
      } as any);

      expect(resolveCommandPath('apalache')).toBe('');
      expect(mockSpawnSync).toHaveBeenCalledTimes(1);
    });

    it('returns command path when which succeeds', () => {
      // First call for commandExists('which')
      mockSpawnSync.mockReturnValueOnce({
        error: undefined,
        status: 0,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 1234,
        output: ['', '', ''],
      } as any);
      // Second call for runCommand('which', [cmd])
      mockSpawnSync.mockReturnValueOnce({
        error: undefined,
        status: 0,
        signal: null,
        stdout: '/usr/local/bin/apalache\n',
        stderr: '',
        pid: 1234,
        output: ['', '/usr/local/bin/apalache\n', ''],
      } as any);

      expect(resolveCommandPath('apalache')).toBe('/usr/local/bin/apalache');
    });

    it('returns empty string when which fails to find command', () => {
      // First call for commandExists('which')
      mockSpawnSync.mockReturnValueOnce({
        error: undefined,
        status: 0,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 1234,
        output: ['', '', ''],
      } as any);
      // Second call for runCommand('which', [cmd])
      mockSpawnSync.mockReturnValueOnce({
        error: undefined,
        status: 1,
        signal: null,
        stdout: '',
        stderr: 'not found',
        pid: 1234,
        output: ['', '', 'not found'],
      } as any);

      expect(resolveCommandPath('nonexistent')).toBe('');
    });

    it('handles multiple paths and returns first line', () => {
      // First call for commandExists('which')
      mockSpawnSync.mockReturnValueOnce({
        error: undefined,
        status: 0,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 1234,
        output: ['', '', ''],
      } as any);
      // Second call for runCommand('which', [cmd])
      mockSpawnSync.mockReturnValueOnce({
        error: undefined,
        status: 0,
        signal: null,
        stdout: '/usr/local/bin/node\n/usr/bin/node\n',
        stderr: '',
        pid: 1234,
        output: ['', '/usr/local/bin/node\n/usr/bin/node\n', ''],
      } as any);

      expect(resolveCommandPath('node')).toBe('/usr/local/bin/node');
    });
  });

  describe('timeout wrapper integration', () => {
    it('handles timeout command wrapping', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: 0,
        signal: null,
        stdout: 'Check successful',
        stderr: '',
        pid: 1234,
        output: ['', 'Check successful', ''],
      } as any);

      const result = runCommand('timeout', ['30s', 'apalache-mc', 'check', 'spec.tla']);
      expect(result.success).toBe(true);
      expect(mockSpawnSync).toHaveBeenCalledWith(
        'timeout',
        ['30s', 'apalache-mc', 'check', 'spec.tla'],
        { encoding: 'utf8' }
      );
    });

    it('detects timeout exit code 124', () => {
      mockSpawnSync.mockReturnValue({
        error: undefined,
        status: 124,
        signal: null,
        stdout: '',
        stderr: '',
        pid: 1234,
        output: ['', '', ''],
      } as any);

      const result = runCommand('timeout', ['1s', 'slow-command']);
      expect(result.success).toBe(false);
      expect(result.status).toBe(124);
    });
  });
});
