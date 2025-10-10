import { defineConfig, defineProject } from 'vitest/config'

export default defineConfig({
  test: {
    include: ['tests/**/*.{test,spec}.{ts,js}'],
    exclude: ['**/.stryker-tmp/**', '**/.stryker-tmp-*/**'],
    reporters: ['default'],
    setupFiles: ['tests/a11y/setup.js'],
    pool: 'threads',
    maxThreads: 4,
  },
  projects: [
    defineProject({
      test: {
        name: 'unit',
        include: ['tests/unit/**/*.test.ts'],
        testTimeout: 10000,
        hookTimeout: 5000,
        pool: 'threads',
      },
    }),
    defineProject({
      test: {
        name: 'integration',
        include: ['tests/integration/**/*.test.ts', 'tests/optimization/system-integration.test.ts'],
        testTimeout: 60000,
        hookTimeout: 30000,
        teardownTimeout: 15000,
        pool: 'forks',        // リソース隔離を強める
        threads: false,       // 競合を避ける
      },
    }),
    defineProject({
      test: {
        name: 'performance',
        include: ['tests/optimization/performance-benchmarks.test.ts'],
        testTimeout: 180000,
        hookTimeout: 60000,
        pool: 'forks',
        threads: false,
      },
    }),
    defineProject({
      test: {
        name: 'quality',
        include: ['tests/quality/**/*.{test,spec}.{ts,js}'],
        testTimeout: 15000,
        hookTimeout: 5000,
        pool: 'threads',
      },
    }),
  ],
})
