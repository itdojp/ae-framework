import { describe, it, expect, vi, beforeAll, beforeEach } from 'vitest';

const spawnSyncMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawnSync: (...args) => spawnSyncMock(...args),
}));

let listProfiles;
let resolveProfile;
let parseArgs;
let runFlake;
let isCliInvocation;

beforeAll(async () => {
  ({
    listProfiles,
    resolveProfile,
    parseArgs,
    runFlake,
    isCliInvocation,
  } = await import('../../scripts/flake/run.mjs'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
});

describe('flake runner profiles', () => {
  it('lists supported profiles', () => {
    expect(listProfiles()).toEqual([
      'detect',
      'detect-quick',
      'detect-thorough',
      'detect-enhanced',
      'detect-enhanced-quick',
      'detect-enhanced-deep',
      'isolate',
      'recover',
      'report',
      'maintenance',
      'remove',
      'list',
    ]);
  });

  it('resolves profile commands', () => {
    expect(resolveProfile('detect')).toEqual([['pnpm', 'run', 'flake:detect']]);
  });

  it('returns null for unknown profiles', () => {
    expect(resolveProfile('unknown')).toBeNull();
  });
});

describe('flake runner arg parsing', () => {
  it('parses profile value', () => {
    const options = parseArgs(['node', 'script', '--profile', 'detect']);
    expect(options.profile).toBe('detect');
    expect(options.profileError).toBe(false);
  });

  it('flags missing profile value', () => {
    const options = parseArgs(['node', 'script', '--profile']);
    expect(options.profileError).toBe(true);
  });
});

describe('flake runner execution', () => {
  it('returns 0 for list', () => {
    const options = parseArgs(['node', 'script', '--list']);
    expect(runFlake(options)).toBe(0);
  });

  it('returns 3 for unknown args', () => {
    const options = parseArgs(['node', 'script', '--bogus']);
    expect(runFlake(options)).toBe(3);
  });

  it('returns 3 for missing profile', () => {
    const options = parseArgs(['node', 'script']);
    expect(runFlake(options)).toBe(3);
  });

  it('returns 2 for unknown profile', () => {
    const options = parseArgs(['node', 'script', '--profile', 'missing']);
    expect(runFlake(options)).toBe(2);
  });

  it('returns 0 for dry-run', () => {
    const options = parseArgs(['node', 'script', '--profile', 'detect', '--dry-run']);
    expect(runFlake(options)).toBe(0);
  });

  it('handles spawn errors', () => {
    spawnSyncMock.mockReturnValueOnce({
      error: Object.assign(new Error('not found'), { code: 'ENOENT' }),
      status: null,
    });
    const options = parseArgs(['node', 'script', '--profile', 'detect']);
    expect(runFlake(options)).toBe(127);
  });

  it('detects non-cli invocation', () => {
    expect(isCliInvocation(['node', '/tmp/unknown'])).toBe(false);
  });
});
