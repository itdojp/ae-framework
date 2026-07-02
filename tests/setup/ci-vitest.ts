import { setMaxListeners } from 'node:events';
import { beforeAll, afterEach, vi } from 'vitest';

const ciFlag = (process.env.CI ?? '').toLowerCase();
const underConservativeEnv = ciFlag === '1' || ciFlag === 'true' || Boolean(process.env.STRYKER_MUTATOR);
const DEFAULT_TEST_TIMEOUT_MS = 60_000;
const DEFAULT_HOOK_TIMEOUT_MS = 30_000;
const DEFAULT_TEARDOWN_TIMEOUT_MS = 10_000;

beforeAll(() => {
  if (underConservativeEnv) {
    vi.setConfig({
      testTimeout: DEFAULT_TEST_TIMEOUT_MS,
      hookTimeout: DEFAULT_HOOK_TIMEOUT_MS,
      teardownTimeout: DEFAULT_TEARDOWN_TIMEOUT_MS,
    });
  }
});

afterEach(() => {
  try {
    vi.unstubAllGlobals();
  } catch {
    // ignore: globals may already be real/unstubbed
  }
  try {
    vi.useRealTimers();
  } catch {
    // ignore: timers may already be real
  }
});

// Avoid MaxListenersExceededWarning noise in CI/property runs
setMaxListeners(0);
if (typeof process.setMaxListeners === 'function') {
  process.setMaxListeners(0);
}
