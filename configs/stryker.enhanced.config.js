import os from 'node:os';

const cpuCount = os.cpus()?.length ?? 1;

/**
 * Targeted Stryker config for EnhancedStateManager quick runs
 */
export default {
  packageManager: 'pnpm',
  reporters: ['clear-text', 'progress', 'json', 'html'],
  mutate: ['src/utils/enhanced-state-manager.ts'],
  ignorePatterns: ['src/utils/enhanced-state-manager.test.ts'],
  testRunner: 'command',
  commandRunner: {
    command: 'pnpm vitest run tests/unit/utils/enhanced-state-manager.test.ts --reporter dot'
  },
  coverageAnalysis: 'perTest',
  incremental: true,
  concurrency: Math.max(1, cpuCount - 1),
  timeoutMS: 30000,
  thresholds: {
    high: 80,
    low: 60,
    break: 0
  }
};
