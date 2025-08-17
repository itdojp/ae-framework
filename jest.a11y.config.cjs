/** @type {import('jest').Config} */
module.exports = {
  displayName: 'Accessibility Tests',
  testMatch: ['<rootDir>/tests/a11y/**/*.test.{js,ts}'],
  testEnvironment: 'jsdom',
  setupFilesAfterEnv: ['<rootDir>/tests/a11y/setup.js'],
  collectCoverageFrom: [
    'packages/ui/**/*.{js,ts,tsx}',
    'apps/web/**/*.{js,ts,tsx}',
    '!**/*.d.ts',
    '!**/*.stories.{js,ts,tsx}',
    '!**/node_modules/**'
  ],
  transform: {
    '^.+\\.(js|jsx|ts|tsx)$': ['babel-jest', {
      presets: [
        ['@babel/preset-env', { targets: { node: 'current' } }],
        ['@babel/preset-react', { runtime: 'automatic' }],
        '@babel/preset-typescript'
      ]
    }]
  },
  moduleNameMapping: {
    '^@/(.*)$': '<rootDir>/packages/ui/src/$1',
    '^@ae-framework/(.*)$': '<rootDir>/packages/$1/src'
  },
  reporters: [
    'default',
    ['jest-junit', {
      outputDirectory: 'reports',
      outputName: 'a11y-junit.xml',
      suiteName: 'Accessibility Tests'
    }]
  ]
};