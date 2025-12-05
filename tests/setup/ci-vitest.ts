import { setMaxListeners } from 'node:events';
import { beforeAll, afterEach, vi } from 'vitest';

const underConservativeEnv = process.env.CI === '1' || Boolean(process.env.STRYKER_MUTATOR);

beforeAll(() => {
  if (underConservativeEnv) {
    vi.setConfig({
      testTimeout: 30_000,
      hookTimeout: 30_000,
      teardownTimeout: 10_000,
    });
  }
});

afterEach(() => {
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
