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
    expect(listProfiles()).toEqual(['lite', 'conformance', 'formal', 'fast', 'full']);
  });

  it('resolves profile commands', () => {
    expect(resolveProfile('conformance')).toEqual([
      ['node', 'scripts/formal/verify-conformance.mjs'],
    ]);
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

  it('parses --json and --out', () => {
    const options = parseArgs(['node', 'script', '--profile', 'fast', '--json', '--out', 'artifacts/summary.json']);
    expect(options.profile).toBe('fast');
    expect(options.json).toBe(true);
    expect(options.out).toBe('artifacts/summary.json');
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

  it('returns 0 when optional step fails in full profile', () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    // build(required)=pass, codex:quickstart(optional)=fail, verify:lite(required)=pass,
    // mbt(optional)=pass, pbt(optional)=pass, mutation(optional)=pass, formal(optional)=pass
    spawnSyncMock
      .mockReturnValueOnce({ status: 0 })
      .mockReturnValueOnce({ status: 1 })
      .mockReturnValueOnce({ status: 0 })
      .mockReturnValueOnce({ status: 0 })
      .mockReturnValueOnce({ status: 0 })
      .mockReturnValueOnce({ status: 0 })
      .mockReturnValueOnce({ status: 0 });

    const options = parseArgs(['node', 'script', '--profile', 'full', '--json']);
    const exitCode = runVerify(options);
    expect(exitCode).toBe(0);

    const payload = JSON.parse(String(consoleLogSpy.mock.calls.at(-1)?.[0] ?? '{}'));
    expect(payload.profile).toBe('full');
    expect(payload.optional_fail_count).toBe(1);
    expect(payload.required_fail_count).toBe(0);
    expect(payload.overall_status).toBe('pass');

    consoleLogSpy.mockRestore();
  });

  it('returns non-zero and skips remaining steps when required step fails', () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    // build(required)=fail -> remaining steps should be skipped
    spawnSyncMock.mockReturnValueOnce({ status: 2 });

    const options = parseArgs(['node', 'script', '--profile', 'fast', '--json']);
    const exitCode = runVerify(options);
    expect(exitCode).toBe(2);

    const payload = JSON.parse(String(consoleLogSpy.mock.calls.at(-1)?.[0] ?? '{}'));
    expect(payload.profile).toBe('fast');
    expect(payload.required_fail_count).toBe(1);
    expect(payload.overall_status).toBe('fail');
    expect(payload.steps[0].status).toBe('failed');
    expect(payload.steps.slice(1).every((step: { status: string }) => step.status === 'skipped')).toBe(true);

    consoleLogSpy.mockRestore();
  });

  it('detects non-cli invocation', () => {
    expect(isCliInvocation(['node', '/tmp/unknown'])).toBe(false);
  });
});
