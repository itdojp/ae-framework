import { describe, it, expect, vi, beforeAll, beforeEach } from 'vitest';

const spawnSyncMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawnSync: (...args) => spawnSyncMock(...args),
}));

let listProfiles;
let resolveProfile;
let parseArgs;
let runTest;
let isCliInvocation;

beforeAll(async () => {
  ({
    listProfiles,
    resolveProfile,
    parseArgs,
    runTest,
    isCliInvocation,
  } = await import('../../scripts/test/run.mjs'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
});

describe('test runner profiles', () => {
  it('lists supported profiles', () => {
    expect(listProfiles()).toEqual([
      'all',
      'fast',
      'fast-plus',
      'unit',
      'integration',
      'perf',
      'ci',
      'ci-stable',
      'ci-lite',
      'ci-extended',
    ]);
  });

  it('resolves profile commands', () => {
    expect(resolveProfile('ci-lite')).toEqual([['pnpm', 'run', 'test:ci:lite']]);
  });

  it('returns null for unknown profiles', () => {
    expect(resolveProfile('unknown')).toBeNull();
  });
});

describe('test runner arg parsing', () => {
  it('parses profile value', () => {
    const options = parseArgs(['node', 'script', '--profile', 'fast']);
    expect(options.profile).toBe('fast');
    expect(options.profileError).toBe(false);
  });

  it('parses profile value with equals form', () => {
    const options = parseArgs(['node', 'script', '--profile=fast']);
    expect(options.profile).toBe('fast');
    expect(options.profileError).toBe(false);
  });

  it('flags missing profile value', () => {
    const options = parseArgs(['node', 'script', '--profile']);
    expect(options.profileError).toBe(true);
  });
});

describe('test runner execution', () => {
  it('returns 0 for help', () => {
    const options = parseArgs(['node', 'script', '--help']);
    expect(runTest(options)).toBe(0);
  });

  it('returns 0 for list', () => {
    const options = parseArgs(['node', 'script', '--list']);
    expect(runTest(options)).toBe(0);
  });

  it('returns 3 for unknown args', () => {
    const options = parseArgs(['node', 'script', '--bogus']);
    expect(runTest(options)).toBe(3);
  });

  it('returns 3 for missing profile', () => {
    const options = parseArgs(['node', 'script']);
    expect(runTest(options)).toBe(3);
  });

  it('returns 2 for unknown profile', () => {
    const options = parseArgs(['node', 'script', '--profile', 'missing']);
    expect(runTest(options)).toBe(2);
  });

  it('returns 0 for dry-run', () => {
    const options = parseArgs(['node', 'script', '--profile', 'fast', '--dry-run']);
    expect(runTest(options)).toBe(0);
  });

  it('returns 0 when command succeeds', () => {
    spawnSyncMock.mockReturnValueOnce({ status: 0 });
    const options = parseArgs(['node', 'script', '--profile', 'fast']);
    expect(runTest(options)).toBe(0);
    expect(spawnSyncMock).toHaveBeenCalled();
  });

  it('returns child exit status for failures', () => {
    spawnSyncMock.mockReturnValueOnce({ status: 9 });
    const options = parseArgs(['node', 'script', '--profile', 'fast']);
    expect(runTest(options)).toBe(9);
  });

  it('handles spawn errors', () => {
    spawnSyncMock.mockReturnValueOnce({
      error: Object.assign(new Error('not found'), { code: 'ENOENT' }),
      status: null,
    });
    const options = parseArgs(['node', 'script', '--profile', 'fast']);
    expect(runTest(options)).toBe(127);
  });

  it('handles spawn errors with non-ENOENT codes', () => {
    spawnSyncMock.mockReturnValueOnce({
      error: Object.assign(new Error('permission denied'), { code: 'EACCES' }),
      status: null,
    });
    const options = parseArgs(['node', 'script', '--profile', 'fast']);
    expect(runTest(options)).toBe(1);
  });

  it('detects non-cli invocation', () => {
    expect(isCliInvocation(['node', '/tmp/unknown'])).toBe(false);
  });
});
