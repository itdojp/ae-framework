import { describe, expect, it } from 'vitest';

import { APITestRunner, type APIAssertion, type APITestConfig } from '../../../../src/integration/runners/api-runner';
import type { TestCase, TestEnvironment } from '../../../../src/integration/types';

const DEFAULT_CONFIG: APITestConfig = {
  timeout: 5000,
  retries: 0,
  validateSchema: true,
  followRedirects: true,
  validateSSL: true,
  maxResponseSize: 1024 * 1024,
  defaultHeaders: {},
};

function createEnvironment(): TestEnvironment {
  return {
    name: 'test',
    apiUrl: 'http://localhost:3000',
    variables: {},
    timeouts: {
      default: 30000,
      api: 10000,
      ui: 5000,
      database: 15000,
    },
    retries: {
      max: 0,
      delay: 0,
    },
  };
}

function createRequestTestCase(assertions: APIAssertion[]): TestCase {
  return {
    id: 'api-inline-assertion-test',
    name: 'API request with inline assertions',
    description: 'Validate inline assertions attached to request steps',
    category: 'integration',
    severity: 'major',
    enabled: true,
    preconditions: [],
    steps: [
      {
        id: 'step-1',
        description: 'Request users endpoint',
        action: 'api:request:GET:/users',
        data: { assertions },
      },
    ],
    expectedResults: ['Request should satisfy inline assertions'],
    fixtures: [],
    dependencies: [],
    tags: [],
    metadata: {
      complexity: 'low',
      stability: 'stable',
      lastUpdated: new Date().toISOString(),
    },
  };
}

describe('APITestRunner', () => {
  it('passes request step when inline assertions are satisfied', async () => {
    const runner = new APITestRunner(DEFAULT_CONFIG);
    const testCase = createRequestTestCase([
      { type: 'status', operator: 'equals', expected: 200 },
      { type: 'body', field: 'name', operator: 'equals', expected: 'Test User' },
    ]);

    const result = await runner.runTest(testCase, createEnvironment());

    expect(result.status).toBe('passed');
    expect(result.steps).toHaveLength(1);
    expect(result.steps[0]?.status).toBe('passed');
    expect(result.error).toBeUndefined();
  });

  it('fails request step when inline assertions are violated', async () => {
    const runner = new APITestRunner(DEFAULT_CONFIG);
    const testCase = createRequestTestCase([
      { type: 'status', operator: 'equals', expected: 201 },
    ]);

    const result = await runner.runTest(testCase, createEnvironment());

    expect(result.status).toBe('failed');
    expect(result.steps).toHaveLength(1);
    expect(result.steps[0]?.status).toBe('failed');
    expect(result.error).toContain('Assertion failed');
  });
});
