import { defineConfig, defineProject } from 'vitest/config'

const mutationScope = process.env.VITEST_MUTATION_SCOPE;
const ciFlag = (process.env.CI ?? '').toLowerCase();
const isCI = ciFlag === '1' || ciFlag === 'true';
const DEFAULT_TEST_TIMEOUT_MS = 60000;
const DEFAULT_HOOK_TIMEOUT_MS = 30000;
const DEFAULT_TEARDOWN_TIMEOUT_MS = 10000;
const isStryker = Boolean(process.env.STRYKER_MUTATOR);
const isCiLike = isCI || isStryker;

function withCiDefaults(config: Record<string, any>) {
  if (!isCiLike) {
    return config;
  }
  return {
    ...config,
    watch: false,
    pool: 'forks',
    threads: false,
    testTimeout: Math.max(DEFAULT_TEST_TIMEOUT_MS, config.testTimeout ?? DEFAULT_TEST_TIMEOUT_MS),
    hookTimeout: Math.max(DEFAULT_HOOK_TIMEOUT_MS, config.hookTimeout ?? DEFAULT_HOOK_TIMEOUT_MS),
    teardownTimeout: Math.max(DEFAULT_TEARDOWN_TIMEOUT_MS, config.teardownTimeout ?? DEFAULT_TEARDOWN_TIMEOUT_MS),
    isolate: config.isolate ?? true,
  };
}

export const baseTestConfig = mutationScope === 'runtime-guard'
  ? withCiDefaults({
      include: [
        'tests/api/runtime-guard.reservations.test.ts',
        'tests/api/server.instrumentation.test.ts',
      ],
      testTimeout: DEFAULT_TEST_TIMEOUT_MS,
      hookTimeout: DEFAULT_HOOK_TIMEOUT_MS,
      teardownTimeout: DEFAULT_TEARDOWN_TIMEOUT_MS,
      exclude: ['**/.stryker-tmp/**', '**/.stryker-tmp-*/**', 'tests/a11y/components.test.js'],
    })
  : withCiDefaults({
      include: ['tests/**/*.{test,spec}.{ts,js}'],
      testTimeout: DEFAULT_TEST_TIMEOUT_MS,
      hookTimeout: DEFAULT_HOOK_TIMEOUT_MS,
      teardownTimeout: DEFAULT_TEARDOWN_TIMEOUT_MS,
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
  setupFiles: ['tests/setup/ci-vitest.ts', 'tests/a11y/setup.js'],
  pool: baseTestConfig.pool ?? 'threads',
  maxThreads: baseTestConfig.maxThreads ?? 4,
};

if (isCiLike) {
  rootTestConfig.pool = 'forks';
  rootTestConfig.threads = false;
  rootTestConfig.watch = false;
  rootTestConfig.testTimeout = baseTestConfig.testTimeout ?? DEFAULT_TEST_TIMEOUT_MS;
  rootTestConfig.hookTimeout = baseTestConfig.hookTimeout ?? DEFAULT_HOOK_TIMEOUT_MS;
  rootTestConfig.teardownTimeout = baseTestConfig.teardownTimeout ?? DEFAULT_TEARDOWN_TIMEOUT_MS;
  rootTestConfig.isolate = true;
}

export default defineConfig({
  test: rootTestConfig,
  projects: projectConfigs,
})
