import { defineConfig, defineProject } from 'vitest/config'

const mutationScope = process.env.VITEST_MUTATION_SCOPE;

const baseTestConfig = mutationScope === 'runtime-guard'
  ? {
      include: [
        'tests/api/runtime-guard.reservations.test.ts',
        'tests/api/server.instrumentation.test.ts',
      ],
      exclude: ['**/.stryker-tmp/**', '**/.stryker-tmp-*/**', 'tests/a11y/components.test.js'],
    }
  : {
      include: ['tests/**/*.{test,spec}.{ts,js}'],
      exclude: ['**/.stryker-tmp/**', '**/.stryker-tmp-*/**', 'tests/a11y/components.test.js'],
    };

const additionalProjects = mutationScope === 'runtime-guard'
  ? []
  : [
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
          pool: 'forks',
          threads: false,
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
    ];

export default defineConfig({
  test: {
    ...baseTestConfig,
    reporters: ['default'],
    setupFiles: ['tests/a11y/setup.js'],
    pool: 'threads',
    maxThreads: 4,
  },
  projects: additionalProjects,
})
