import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';

const baseEnv = {
  AE_GH_RETRY_NO_SLEEP: process.env.AE_GH_RETRY_NO_SLEEP,
  AE_GH_RETRY_MAX_ATTEMPTS: process.env.AE_GH_RETRY_MAX_ATTEMPTS,
  AE_GH_RETRY_INITIAL_DELAY_MS: process.env.AE_GH_RETRY_INITIAL_DELAY_MS,
  AE_GH_RETRY_MAX_DELAY_MS: process.env.AE_GH_RETRY_MAX_DELAY_MS,
};

const resetEnv = () => {
  for (const [key, value] of Object.entries(baseEnv)) {
    if (value === undefined) {
      delete process.env[key];
    } else {
      process.env[key] = value;
    }
  }
};

describe('gh-exec', () => {
  beforeEach(() => {
    resetEnv();
  });

  afterEach(() => {
    resetEnv();
    vi.restoreAllMocks();
    vi.resetModules();
  });

  it('detects retryable GitHub API failures', async () => {
    const { __testOnly_shouldRetry } = await import('../../../scripts/ci/lib/gh-exec.mjs');

    expect(__testOnly_shouldRetry('HTTP 429: Too Many Requests')).toBe(true);
    expect(__testOnly_shouldRetry('You have exceeded a secondary rate limit.')).toBe(true);
    expect(__testOnly_shouldRetry('abuse detection mechanism')).toBe(true);
    expect(__testOnly_shouldRetry('HTTP 403: Resource not accessible by integration')).toBe(false);
  });

  it('retries execGh on retryable failures', async () => {
    process.env.AE_GH_RETRY_NO_SLEEP = '1';
    process.env.AE_GH_RETRY_MAX_ATTEMPTS = '3';
    process.env.AE_GH_RETRY_INITIAL_DELAY_MS = '1';
    process.env.AE_GH_RETRY_MAX_DELAY_MS = '1';

    let attempt = 0;
    const execFileSyncMock = vi.fn(() => {
      attempt += 1;
      if (attempt < 3) {
        const error = new Error('HTTP 429: Too Many Requests');
        (error as any).stderr = 'HTTP 429: Too Many Requests';
        throw error;
      }
      return 'ok';
    });

    vi.doMock('node:child_process', () => ({
      execFileSync: execFileSyncMock,
    }));

    const { execGh } = await import('../../../scripts/ci/lib/gh-exec.mjs');
    expect(execGh(['api', 'rate_limit'])).toBe('ok');
    expect(execFileSyncMock).toHaveBeenCalledTimes(3);
  });

  it('does not retry execGh on non-retryable failures', async () => {
    process.env.AE_GH_RETRY_NO_SLEEP = '1';
    process.env.AE_GH_RETRY_MAX_ATTEMPTS = '5';

    const execFileSyncMock = vi.fn(() => {
      const error = new Error('HTTP 403: Forbidden');
      (error as any).stderr = 'HTTP 403: Forbidden';
      throw error;
    });

    vi.doMock('node:child_process', () => ({
      execFileSync: execFileSyncMock,
    }));

    const { execGh } = await import('../../../scripts/ci/lib/gh-exec.mjs');
    expect(() => execGh(['api', 'rate_limit'])).toThrow(/Forbidden/);
    expect(execFileSyncMock).toHaveBeenCalledTimes(1);
  });
});
