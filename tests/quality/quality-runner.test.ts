import { describe, it, expect, vi, beforeAll, beforeEach } from 'vitest';

const spawnSyncMock = vi.fn();

vi.mock('node:child_process', () => ({
  spawnSync: (...args) => spawnSyncMock(...args),
}));

let listProfiles;
let resolveProfile;
let parseArgs;
let runQuality;
let isCliInvocation;

beforeAll(async () => {
  ({
    listProfiles,
    resolveProfile,
    parseArgs,
    runQuality,
    isCliInvocation,
  } = await import('../../scripts/quality/run.mjs'));
});

beforeEach(() => {
  spawnSyncMock.mockReset();
});

describe('quality runner profiles', () => {
  it('lists supported profiles', () => {
    expect(listProfiles()).toEqual(['all', 'gates', 'policy']);
  });

  it('resolves profile commands', () => {
    expect(resolveProfile('gates')).toEqual([['pnpm', 'run', 'quality:gates']]);
  });

  it('returns null for unknown profiles', () => {
    expect(resolveProfile('unknown')).toBeNull();
  });
});

describe('quality runner arg parsing', () => {
  it('parses profile value', () => {
    const options = parseArgs(['node', 'script', '--profile', 'all']);
    expect(options.profile).toBe('all');
    expect(options.profileError).toBe(false);
  });

  it('flags missing profile value', () => {
    const options = parseArgs(['node', 'script', '--profile']);
    expect(options.profileError).toBe(true);
  });
});

describe('quality runner execution', () => {
  it('returns 0 for list', () => {
    const options = parseArgs(['node', 'script', '--list']);
    expect(runQuality(options)).toBe(0);
  });

  it('returns 3 for unknown args', () => {
    const options = parseArgs(['node', 'script', '--bogus']);
    expect(runQuality(options)).toBe(3);
  });

  it('returns 3 for missing profile', () => {
    const options = parseArgs(['node', 'script']);
    expect(runQuality(options)).toBe(3);
  });

  it('returns 2 for unknown profile', () => {
    const options = parseArgs(['node', 'script', '--profile', 'missing']);
    expect(runQuality(options)).toBe(2);
  });

  it('returns 0 for dry-run', () => {
    const options = parseArgs(['node', 'script', '--profile', 'gates', '--dry-run']);
    expect(runQuality(options)).toBe(0);
  });

  it('handles spawn errors', () => {
    spawnSyncMock.mockReturnValueOnce({
      error: Object.assign(new Error('not found'), { code: 'ENOENT' }),
      status: null,
    });
    const options = parseArgs(['node', 'script', '--profile', 'gates']);
    expect(runQuality(options)).toBe(127);
  });

  it('detects non-cli invocation', () => {
    expect(isCliInvocation(['node', '/tmp/unknown'])).toBe(false);
  });
});
