export default {
  packageManager: 'npm',
  reporters: ['progress', 'json'],
  testRunner: 'command',
  commandRunner: {
    command: './scripts/testing/run-mutation-quick.sh'
  },
  coverageAnalysis: 'off',
  mutate: [
    'src/api/server.ts',
    'src/utils/enhanced-state-manager.ts'
  ],
};
