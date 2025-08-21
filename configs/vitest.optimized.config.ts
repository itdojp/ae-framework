import { defineConfig } from 'vitest/config';

export default defineConfig({
  "test": {
    "testTimeout": 60000,
    "hookTimeout": 30000,
    "teardownTimeout": 30000,
    "pool": "threads",
    "poolOptions": {
      "threads": {
        "maxThreads": 4,
        "minThreads": 1
      }
    },
    "restoreMocks": true,
    "clearMocks": true,
    "resetMocks": true,
    "resetModules": true,
    "isolate": true,
    "reporter": [
      "verbose"
    ],
    "env": {
      "NODE_ENV": "test",
      "CI": "false",
      "TEST_TIMEOUT": "60000",
      "DISABLE_ANIMATIONS": "false"
    },
    "retry": 1,
    "logHeapUsage": true,
    "coverage": {
      "enabled": true,
      "provider": "v8",
      "reporter": [
        "text",
        "json",
        "html"
      ],
      "exclude": [
        "node_modules/**",
        "dist/**",
        "coverage/**",
        "tests/**",
        "**/*.test.*",
        "**/*.spec.*"
      ]
    },
    "exclude": [
      "tests/**/*.flaky.test.*",
      "tests/**/flaky/**",
      "node_modules/**"
    ]
  }
});
