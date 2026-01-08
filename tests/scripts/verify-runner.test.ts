import { describe, it, expect, vi, beforeAll, beforeEach } from 'vitest';

const spawnSyncMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawnSync: (...args) => spawnSyncMock(...args),
}));

let listProfiles;
let resolveProfile;
let parseArgs;
let runVerify;
let isCliInvocation;

beforeAll(async () => {
  ({
    listProfiles,
    resolveProfile,
    parseArgs,
    runVerify,
    isCliInvocation,
  } = await import('../../scripts/verify/run.mjs'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
});

describe('verify runner profiles', () => {
  it('lists supported profiles', () => {
    expect(listProfiles()).toEqual(['lite', 'conformance', 'formal']);
  });

  it('resolves profile commands', () => {
    expect(resolveProfile('conformance')).toEqual([['pnpm', 'run', 'verify:conformance']]);
  });

  it('returns null for unknown profiles', () => {
    expect(resolveProfile('unknown')).toBeNull();
  });
});

describe('verify runner arg parsing', () => {
  it('parses profile value', () => {
    const options = parseArgs(['node', 'script', '--profile', 'lite']);
    expect(options.profile).toBe('lite');
    expect(options.profileError).toBe(false);
  });

  it('flags missing profile value', () => {
    const options = parseArgs(['node', 'script', '--profile']);
    expect(options.profileError).toBe(true);
  });
});

describe('verify runner execution', () => {
  it('returns 0 for list', () => {
    const options = parseArgs(['node', 'script', '--list']);
    expect(runVerify(options)).toBe(0);
  });

  it('returns 3 for unknown args', () => {
    const options = parseArgs(['node', 'script', '--bogus']);
    expect(runVerify(options)).toBe(3);
  });

  it('returns 3 for missing profile', () => {
    const options = parseArgs(['node', 'script']);
    expect(runVerify(options)).toBe(3);
  });

  it('returns 2 for unknown profile', () => {
    const options = parseArgs(['node', 'script', '--profile', 'missing']);
    expect(runVerify(options)).toBe(2);
  });

  it('returns 0 for dry-run', () => {
    const options = parseArgs(['node', 'script', '--profile', 'conformance', '--dry-run']);
    expect(runVerify(options)).toBe(0);
  });

  it('handles spawn errors', () => {
    spawnSyncMock.mockReturnValueOnce({
      error: Object.assign(new Error('not found'), { code: 'ENOENT' }),
      status: null,
    });
    const options = parseArgs(['node', 'script', '--profile', 'conformance']);
    expect(runVerify(options)).toBe(127);
  });

  it('detects non-cli invocation', () => {
    expect(isCliInvocation(['node', '/tmp/unknown'])).toBe(false);
  });
});
