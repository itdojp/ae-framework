import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    testTimeout: 120000,
    hookTimeout: 60000,
    teardownTimeout: 30000,
    pool: 'threads',
    poolOptions: {
      threads: {
        maxThreads: 2,
        minThreads: 1
      }
    },
    restoreMocks: true,
    clearMocks: true,
    resetMocks: true,
    resetModules: true,
    retry: 2,
    reporter: ['verbose'],
    exclude: [
      'tests/optimization/system-integration.test.ts',
      'tests/**/*.flaky.test.*',
      'tests/**/*.e2e.test.*'
    ]
  }
});
