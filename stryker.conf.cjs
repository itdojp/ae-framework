/** @type {import('@stryker-mutator/api/core').StrykerOptions} */
module.exports = {
  packageManager: 'pnpm',
  testRunner: 'vitest',
  mutate: [
    'src/**/*.ts',
    '!src/**/*.test.ts',
    '!src/**/*.spec.ts',
    '!src/**/*.d.ts',
    '!src/**/__tests__/**',
    '!packages/**/*'
  ],
  vitest: {
    configFile: 'vitest.config.ts',
  },
  coverageAnalysis: 'perTest',
  timeoutMS: 120000,
  tempDirName: '.stryker-tmp',
  reporters: ['html', 'progress', 'dashboard'],
  plugins: ['@stryker-mutator/vitest-runner'],
  disableTypeChecks: '{src,tests}/**/*.{ts,tsx,js,jsx}',
  thresholds: {
    high: 80,
    low: 60,
    break: 0,
  },
  concurrency: 2,
};
