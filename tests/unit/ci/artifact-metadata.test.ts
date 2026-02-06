import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';

const baseEnv = { ...process.env };

const resetEnv = () => {
  process.env = { ...baseEnv };
};

describe('buildArtifactMetadata', () => {
  beforeEach(() => {
    resetEnv();
  });

  afterEach(() => {
    resetEnv();
    vi.restoreAllMocks();
    vi.resetModules();
  });

  it('builds metadata from env and tool versions', async () => {
    process.env.GIT_COMMIT = 'abc1234';
    process.env.GITHUB_HEAD_REF = 'feature/metadata';
    process.env.RUNNER_NAME = 'runner-1';
    process.env.RUNNER_OS = 'Linux';
    process.env.RUNNER_ARCH = 'X64';
    process.env.CI = 'true';

    const { buildArtifactMetadata } = await import('../../../scripts/ci/lib/artifact-metadata.mjs');
    const now = new Date('2025-01-02T03:04:05.006Z');
    const metadata = buildArtifactMetadata({ now, toolVersions: { pnpm: '10.1.0' } });

    expect(metadata.generatedAtUtc).toBe(now.toISOString());
    expect(metadata.timezoneOffset).toMatch(/^[+-]\d{2}:\d{2}$/);
    expect(metadata.generatedAtLocal.endsWith(metadata.timezoneOffset)).toBe(true);
    expect(metadata.gitCommit).toBe('abc1234');
    expect(metadata.branch).toBe('feature/metadata');
    expect(metadata.runner).toEqual({
      name: 'runner-1',
      os: 'Linux',
      arch: 'X64',
      ci: true
    });
    expect(metadata.toolVersions.node).toBe(process.version);
    expect(metadata.toolVersions.pnpm).toBe('10.1.0');
  });

  it('returns null commit/branch when git commands fail and env is absent', async () => {
    delete process.env.GIT_COMMIT;
    delete process.env.GITHUB_SHA;
    delete process.env.COMMIT_SHA;
    delete process.env.GITHUB_HEAD_REF;
    delete process.env.GITHUB_REF_NAME;
    delete process.env.GITHUB_REF;
    delete process.env.BRANCH_NAME;
    delete process.env.GIT_BRANCH;

    vi.doMock('node:child_process', () => ({
      execSync: vi.fn(() => {
        throw new Error('git unavailable');
      })
    }));

    const { buildArtifactMetadata } = await import('../../../scripts/ci/lib/artifact-metadata.mjs');
    const metadata = buildArtifactMetadata({ now: new Date('2025-01-02T03:04:05.006Z') });

    expect(metadata.gitCommit).toBeNull();
    expect(metadata.branch).toBeNull();
  });
});
