import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    include: ['tests/property/**/*.{test,spec}.{ts,js}'],
    setupFiles: ['tests/setup/ci-vitest.ts'],
    passWithNoTests: false,
  },
});
