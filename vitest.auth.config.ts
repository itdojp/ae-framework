import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    include: [
      'tests/services/auth-service.test.ts',
      'tests/security/auth-security.test.ts',
      'tests/integration/auth-integration.test.ts',
      'tests/error-handling/auth-error-handling.test.ts',
      'tests/property/auth-property.test.ts',
      'tests/e2e/auth-e2e.test.ts'
    ],
    environment: 'node',
    globals: true,
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
      exclude: [
        'node_modules/',
        'dist/',
        'tests/',
        '**/*.test.ts',
        '**/*.config.ts'
      ],
      include: [
        'src/services/auth-service.ts'
      ],
      thresholds: {
        global: {
          branches: 80,
          functions: 90,
          lines: 85,
          statements: 85
        }
      }
    },
    testTimeout: 30000,
    hookTimeout: 10000,
    teardownTimeout: 10000,
    reporters: ['verbose'],
    pool: 'forks',
    poolOptions: {
      forks: {
        singleFork: true
      }
    }
  }
});