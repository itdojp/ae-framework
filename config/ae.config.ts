export default {
  tddGuard: {
    enabled: true,
    onlyChanged: true,
    changedSince: 'origin/main',
    include: ['src/**/*.ts', 'tests/**/*.ts'],
    exclude: ['**/*.md'],
    allowSkipWithEnv: 'AE_SKIP_GUARD',
    ciOnly: false
  },
  qa: {
    coverageThreshold: {
      branches: 90,
      lines: 90,
      functions: 90,
      statements: 90
    }
  },
  bench: {
    warmupMs: 300,
    iterations: 30,
    seed: 12345
  }
};