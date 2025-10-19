import { defineConfig, defineProject } from 'vitest/config'

const mutationScope = process.env.VITEST_MUTATION_SCOPE;
const isCI = process.env.CI === '1';

function withCiDefaults(config: Record<string, any>) {
  if (!isCI) {
    return config;
  }
  return {
    ...config,
    watch: false,
    pool: 'forks',
    threads: false,
    testTimeout: Math.max(30000, config.testTimeout ?? 30000),
    hookTimeout: Math.max(30000, config.hookTimeout ?? 30000),
    teardownTimeout: Math.max(10000, config.teardownTimeout ?? 10000),
    isolate: config.isolate ?? true,
  };
}

export const baseTestConfig = mutationScope === 'runtime-guard'
  ? withCiDefaults({
      include: [
        'tests/api/runtime-guard.reservations.test.ts',
        'tests/api/server.instrumentation.test.ts',
      ],
      exclude: ['**/.stryker-tmp/**', '**/.stryker-tmp-*/**', 'tests/a11y/components.test.js'],
    })
  : withCiDefaults({
      include: ['tests/**/*.{test,spec}.{ts,js}'],
      exclude: ['**/.stryker-tmp/**', '**/.stryker-tmp-*/**', 'tests/a11y/components.test.js'],
    });

export const projectConfigs = mutationScope === 'runtime-guard'
  ? []
  : [
      defineProject({
        test: withCiDefaults({
          name: 'unit',
          include: ['tests/unit/**/*.test.ts'],
          testTimeout: 10000,
          hookTimeout: 5000,
          pool: 'threads',
        }),
      }),
      defineProject({
        test: withCiDefaults({
          name: 'integration',
          include: ['tests/integration/**/*.test.ts', 'tests/optimization/system-integration.test.ts'],
          testTimeout: 60000,
          hookTimeout: 30000,
          teardownTimeout: 15000,
          pool: 'forks',
          threads: false,
        }),
      }),
      defineProject({
        test: withCiDefaults({
          name: 'performance',
          include: ['tests/optimization/performance-benchmarks.test.ts'],
          testTimeout: 180000,
          hookTimeout: 60000,
          pool: 'forks',
          threads: false,
        }),
      }),
      defineProject({
        test: withCiDefaults({
          name: 'quality',
          include: ['tests/quality/**/*.{test,spec}.{ts,js}'],
          testTimeout: 15000,
          hookTimeout: 5000,
          pool: 'threads',
        }),
      }),
    ];

export const rootTestConfig = {
  ...baseTestConfig,
  reporters: ['default'],
  setupFiles: ['tests/a11y/setup.js'],
  pool: baseTestConfig.pool ?? 'threads',
  maxThreads: baseTestConfig.maxThreads ?? 4,
};

if (isCI) {
  rootTestConfig.pool = 'forks';
  rootTestConfig.threads = false;
  rootTestConfig.watch = false;
  rootTestConfig.testTimeout = baseTestConfig.testTimeout ?? 30000;
  rootTestConfig.hookTimeout = baseTestConfig.hookTimeout ?? 30000;
  rootTestConfig.teardownTimeout = baseTestConfig.teardownTimeout ?? 10000;
  rootTestConfig.isolate = true;
}

export default defineConfig({
  test: rootTestConfig,
  projects: projectConfigs,
})
