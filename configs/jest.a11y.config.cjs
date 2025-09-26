const path = require('node:path');

const rootDir = path.resolve(__dirname, '..');

/** @type {import('jest').Config} */
module.exports = {
  displayName: 'Accessibility Tests',
  rootDir,
  testMatch: ['<rootDir>/tests/a11y/**/*.test.{js,ts}'],
  testEnvironment: 'node',
  setupFilesAfterEnv: ['<rootDir>/tests/a11y/setup.js'],
  transform: {
    '^.+\\.(js|jsx|ts|tsx)$': ['babel-jest', {
      presets: [
        ['@babel/preset-env', { targets: { node: 'current' } }],
        '@babel/preset-typescript'
      ]
    }]
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
