import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    include: [
      'tests/property/**/*.pbt.test.ts',
      'tests/property/**/*.property.test.ts',
    ],
    setupFiles: ['tests/setup/ci-vitest.ts', 'tests/a11y/setup.js'],
    passWithNoTests: false,
  },
});
