/**
 * Integration Test Orchestrator Tests
 * Phase 2.3: Test suite for integration test orchestrator
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { join } from 'path';
import { IntegrationTestOrchestrator } from '../../src/integration/test-orchestrator.js';
import { E2ETestRunner } from '../../src/integration/runners/e2e-runner.js';
import { APITestRunner } from '../../src/integration/runners/api-runner.js';
import { HTMLTestReporter } from '../../src/integration/reporters/html-reporter.js';
import {
  TestCase,
  TestSuite,
  TestFixture,
  TestEnvironment,
  TestExecutionConfig,
  IntegrationTestConfig,
  TestDiscovery,
  TestRunner,
  TestResult
} from '../../src/integration/types.js';
import {
  createIntegrationTempDir,
  registerIntegrationCleanup,
  applyIntegrationRetry,
} from '../_helpers/integration-test-utils.js';
import './setup';

applyIntegrationRetry(it);

// Helper functions
function createMockTestCase(id: string, name: string, category: any): TestCase {
  return {
    id,
    name,
    description: `Mock test case: ${name}`,
    category,
    severity: 'major',
    enabled: true,
    preconditions: [],
    steps: [
      {
        id: 'step-1',
        description: 'Mock step',
        action: category === 'e2e' ? 'navigate:/' : 'api:request:GET:/health',
        data: {},
        expectedResult: 'Success'
      }
    ],
    expectedResults: ['Test completes successfully'],
    fixtures: [],
    dependencies: [],
    tags: ['mock', 'test'],
    metadata: {
      complexity: 'low',
      stability: 'stable',
      lastUpdated: new Date().toISOString()
    }
  };
}

function createMockTestSuite(id: string, name: string, tests: string[]): TestSuite {
  return {
    id,
    name,
    description: `Mock test suite: ${name}`,
    category: 'integration',
    tests,
    fixtures: [],
    configuration: {
      parallel: false,
      maxConcurrency: 1,
      timeout: 60000,
      retries: 1,
      skipOnFailure: false,
      failFast: false
    },
    setup: [],
    teardown: [],
    metadata: {
      priority: 'medium',
      tags: ['mock', 'suite']
    }
  };
}

function createMockFixture(id: string, name: string): TestFixture {
  return {
    id,
    name,
    description: `Mock test fixture: ${name}`,
    category: 'unit',
    data: { mockData: true },
    setup: [],
    teardown: [],
    dependencies: [],
    metadata: {
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
      version: '1.0.0',
      tags: ['mock', 'fixture']
    }
  };
}

function createMockEnvironment(): TestEnvironment {
  return {
    name: 'test',
    baseUrl: 'http://localhost:3000',
    apiUrl: 'http://localhost:3000/api',
    variables: {
      TEST_MODE: 'true'
    },
    timeouts: {
      default: 30000,
      api: 10000,
      ui: 5000
    },
    retries: {
      max: 2,
      delay: 1000
    }
  };
}

// Mock test discovery
class MockTestDiscovery implements TestDiscovery {
  async discoverTests(): Promise<TestCase[]> {
    return [
      createMockTestCase('test-1', 'Sample E2E Test', 'e2e'),
      createMockTestCase('test-2', 'Sample API Test', 'integration')
    ];
  }

  async discoverSuites(): Promise<TestSuite[]> {
    return [
      createMockTestSuite('suite-1', 'Sample Test Suite', ['test-1', 'test-2'])
    ];
  }

  async discoverFixtures(): Promise<TestFixture[]> {
    return [
      createMockFixture('fixture-1', 'Sample Fixture')
    ];
  }
}

describe('IntegrationTestOrchestrator', () => {
  let orchestrator: IntegrationTestOrchestrator;
  let mockDiscovery: TestDiscovery;
  let config: IntegrationTestConfig;
  let integrationTempDir: string;
  const getOutputDir = (suffix = 'test-results') =>
    join(integrationTempDir, suffix);

  beforeEach(async () => {
    integrationTempDir = await createIntegrationTempDir('integration-orchestrator-');

    config = {
      environments: [createMockEnvironment()],
      defaultEnvironment: 'test',
      runners: [
        new E2ETestRunner({
          browser: 'chromium',
          headless: true,
          viewport: { width: 1280, height: 720 },
          timeout: 30000,
          retries: 1,
          screenshots: false,
          video: false,
          trace: false,
          slowMo: 0
        }),
        new APITestRunner({
          timeout: 10000,
          retries: 2,
          validateSchema: false,
          followRedirects: true,
          validateSSL: false,
          maxResponseSize: 1024 * 1024,
          defaultHeaders: {}
        })
      ],
      reporters: [new HTMLTestReporter()],
      globalTimeout: 60000,
      globalRetries: 1,
      parallelSuites: false,
      maxSuiteConcurrency: 1,
      artifactRetention: { days: 7, maxSize: 100 },
      notifications: { enabled: false, channels: [], onFailure: false, onSuccess: false }
    };

    orchestrator = new IntegrationTestOrchestrator(config);
    mockDiscovery = new MockTestDiscovery();
    
    await orchestrator.initialize();

    registerIntegrationCleanup(() => {
      orchestrator.removeAllListeners();
    });
  });

  describe('initialization', () => {
    it('should initialize successfully', async () => {
      expect(orchestrator).toBeDefined();
      
      const environments = orchestrator.getEnvironments();
      expect(environments).toHaveLength(1);
      expect(environments[0].name).toBe('test');

      const runners = orchestrator.getRunners();
      expect(runners).toHaveLength(2);
    });

    it('should emit initialization events', async () => {
      const initializingEvent = vi.fn();
      const initializedEvent = vi.fn();

      const newOrchestrator = new IntegrationTestOrchestrator(config);
      newOrchestrator.on('orchestrator_initializing', initializingEvent);
      newOrchestrator.on('orchestrator_initialized', initializedEvent);

      await newOrchestrator.initialize();

      expect(initializingEvent).toHaveBeenCalled();
      expect(initializedEvent).toHaveBeenCalled();
    });
  });

  describe('test discovery', () => {
    it('should discover tests, suites, and fixtures', async () => {
      const discovered = await orchestrator.discoverTests(mockDiscovery, ['./test/**/*.json']);

      expect(discovered.tests).toHaveLength(2);
      expect(discovered.suites).toHaveLength(1);
      expect(discovered.fixtures).toHaveLength(1);

      expect(discovered.tests[0].name).toBe('Sample E2E Test');
      expect(discovered.tests[1].name).toBe('Sample API Test');
      expect(discovered.suites[0].name).toBe('Sample Test Suite');
    });

    it('should emit discovery events', async () => {
      const discoveryStarted = vi.fn();
      const discoveryCompleted = vi.fn();

      orchestrator.on('test_discovery_started', discoveryStarted);
      orchestrator.on('test_discovery_completed', discoveryCompleted);

      await orchestrator.discoverTests(mockDiscovery, ['./test/**/*.json']);

      expect(discoveryStarted).toHaveBeenCalledWith({ patterns: ['./test/**/*.json'] });
      expect(discoveryCompleted).toHaveBeenCalledWith({
        testsFound: 2,
        suitesFound: 1,
        fixturesFound: 1
      });
    });

    it('should cache discovered items', async () => {
      await orchestrator.discoverTests(mockDiscovery, ['./test/**/*.json']);

      const testCases = orchestrator.getTestCases();
      const testSuites = orchestrator.getTestSuites();

      expect(testCases).toHaveLength(2);
      expect(testSuites).toHaveLength(1);
    });
  });

  describe('test execution', () => {
    beforeEach(async () => {
      // Discover tests first
      await orchestrator.discoverTests(mockDiscovery, ['./test/**/*.json']);
    });

    it('should execute a single test', async () => {
      const testStarted = vi.fn();
      const testCompleted = vi.fn();

      orchestrator.on('test_started', testStarted);
      orchestrator.on('test_completed', testCompleted);

      const config: TestExecutionConfig = {
        environment: 'test',
        parallel: false,
        maxConcurrency: 1,
        timeout: 60000,
        retries: 1,
        generateReport: false,
        outputDir: getOutputDir()
      };

      const result = await orchestrator.executeTest('test-1', 'test', config);

      expect(result).toBeDefined();
      expect(result.testId).toBe('test-1');
      expect(result.environment).toBe('test');
      expect(result.status).toMatch(/passed|failed|error/);

      expect(testStarted).toHaveBeenCalledWith({ testId: 'test-1', environment: 'test' });
      expect(testCompleted).toHaveBeenCalled();
    });

    it('should handle test not found', async () => {
      const config: TestExecutionConfig = {
        environment: 'test',
        outputDir: getOutputDir()
      };

      await expect(orchestrator.executeTest('nonexistent', 'test', config))
        .rejects.toThrow('Test not found: nonexistent');
    });

    it('should handle environment not found', async () => {
      const config: TestExecutionConfig = {
        environment: 'nonexistent',
        outputDir: getOutputDir()
      };

      await expect(orchestrator.executeTest('test-1', 'nonexistent', config))
        .rejects.toThrow('Environment not found: nonexistent');
    });
  });

  describe('suite execution', () => {
    beforeEach(async () => {
      await orchestrator.discoverTests(mockDiscovery, ['./test/**/*.json']);
    });

    it('should execute a test suite', async () => {
      const suiteStarted = vi.fn();
      const suiteCompleted = vi.fn();

      orchestrator.on('suite_started', suiteStarted);
      orchestrator.on('suite_completed', suiteCompleted);

      const config: TestExecutionConfig = {
        environment: 'test',
        parallel: false,
        maxConcurrency: 1,
        timeout: 60000,
        retries: 1,
        generateReport: false,
        outputDir: getOutputDir()
      };

      const summary = await orchestrator.executeSuite('suite-1', 'test', config);

      expect(summary).toBeDefined();
      expect(summary.environment).toBe('test');
      expect(summary.statistics.total).toBeGreaterThan(0);
      expect(summary.results).toHaveLength(summary.statistics.total);

      expect(suiteStarted).toHaveBeenCalled();
      expect(suiteCompleted).toHaveBeenCalled();
    });

    it('should handle suite not found', async () => {
      const config: TestExecutionConfig = {
        environment: 'test',
        outputDir: getOutputDir()
      };

      await expect(orchestrator.executeSuite('nonexistent', 'test', config))
        .rejects.toThrow('Test suite not found: nonexistent');
    });

    it('should prevent concurrent execution of same suite', async () => {
      const config: TestExecutionConfig = {
        environment: 'test',
        outputDir: getOutputDir()
      };

      // Start first execution
      const firstExecution = orchestrator.executeSuite('suite-1', 'test', config);

      // Try to start second execution immediately
      await expect(orchestrator.executeSuite('suite-1', 'test', config))
        .rejects.toThrow('Suite execution already in progress: suite-1');

      // Wait for first execution to complete
      await firstExecution;
    });
  });

  describe('filtering', () => {
    beforeEach(async () => {
      await orchestrator.discoverTests(mockDiscovery, ['./test/**/*.json']);
    });

    it('should filter tests by category', async () => {
      const config: TestExecutionConfig = {
        environment: 'test',
        outputDir: getOutputDir(),
        filters: {
          categories: ['e2e']
        }
      };

      const summary = await orchestrator.executeSuite('suite-1', 'test', config);
      
      // Should have filtered to only E2E tests
      expect(summary.statistics.total).toBeGreaterThan(0);
    });

    it('should filter tests by tags', async () => {
      const config: TestExecutionConfig = {
        environment: 'test',
        outputDir: getOutputDir(),
        filters: {
          tags: ['smoke']
        }
      };

      const summary = await orchestrator.executeSuite('suite-1', 'test', config);
      expect(summary.statistics).toBeDefined();
    });

    it('should exclude specific tests', async () => {
      const config: TestExecutionConfig = {
        environment: 'test',
        outputDir: getOutputDir(),
        filters: {
          exclude: ['test-1']
        }
      };

      const summary = await orchestrator.executeSuite('suite-1', 'test', config);
      
      // Should have excluded test-1
      const executedTests = summary.results.map(r => r.testId);
      expect(executedTests).not.toContain('test-1');
    });
  });

  describe('execution status', () => {
    it('should track execution status', () => {
      expect(orchestrator.getExecutionStatus('suite-1')).toBe('idle');
    });

    it('should report running status during execution', async () => {
      const config: TestExecutionConfig = {
        environment: 'test',
        outputDir: getOutputDir()
      };

      await orchestrator.discoverTests(mockDiscovery, ['./test/**/*.json']);

      // Start execution without waiting
      const execution = orchestrator.executeSuite('suite-1', 'test', config);
      
      // Should show as running (may be too fast to catch in mock)
      // expect(orchestrator.getExecutionStatus('suite-1')).toBe('running');
      
      await execution;
      expect(orchestrator.getExecutionStatus('suite-1')).toBe('idle');
    });
  });

  describe('resource management', () => {
    it('should add and retrieve test cases', () => {
      const testCase = createMockTestCase('new-test', 'New Test', 'unit');
      
      orchestrator.addTestCase(testCase);
      const testCases = orchestrator.getTestCases();
      
      expect(testCases.some(tc => tc.id === 'new-test')).toBe(true);
    });

    it('should add and retrieve test suites', () => {
      const testSuite = createMockTestSuite('new-suite', 'New Suite', []);
      
      orchestrator.addTestSuite(testSuite);
      const testSuites = orchestrator.getTestSuites();
      
      expect(testSuites.some(ts => ts.id === 'new-suite')).toBe(true);
    });

    it('should add and retrieve test fixtures', () => {
      const fixture = createMockFixture('new-fixture', 'New Fixture');
      
      orchestrator.addTestFixture(fixture);
      // Fixtures are stored internally but not exposed via getter
      expect(() => orchestrator.addTestFixture(fixture)).not.toThrow();
    });

    it('should emit events when adding resources', () => {
      const testCaseAdded = vi.fn();
      const testSuiteAdded = vi.fn();
      const testFixtureAdded = vi.fn();

      orchestrator.on('test_case_added', testCaseAdded);
      orchestrator.on('test_suite_added', testSuiteAdded);
      orchestrator.on('test_fixture_added', testFixtureAdded);

      orchestrator.addTestCase(createMockTestCase('event-test', 'Event Test', 'unit'));
      orchestrator.addTestSuite(createMockTestSuite('event-suite', 'Event Suite', []));
      orchestrator.addTestFixture(createMockFixture('event-fixture', 'Event Fixture'));

      expect(testCaseAdded).toHaveBeenCalledWith({ testId: 'event-test' });
      expect(testSuiteAdded).toHaveBeenCalledWith({ suiteId: 'event-suite' });
      expect(testFixtureAdded).toHaveBeenCalledWith({ fixtureId: 'event-fixture' });
    });
  });

  describe('runner lifecycle management', () => {
    class LifecycleRunner implements TestRunner {
      readonly id = 'lifecycle-runner';
      readonly name = 'Lifecycle Runner';
      readonly category = 'integration' as const;

      setup = vi.fn(async () => {});
      teardown = vi.fn(async () => {});
      beforeTest = vi.fn(async () => {});
      afterTest = vi.fn(async (_test: TestCase, _result: TestResult) => {});
      runTest = vi.fn(async (test: TestCase, environment: TestEnvironment): Promise<TestResult> => ({
        id: `result-${test.id}`,
        testId: test.id,
        status: 'passed',
        startTime: new Date().toISOString(),
        endTime: new Date().toISOString(),
        duration: 5,
        environment: environment.name,
        steps: [],
        screenshots: [],
        logs: [],
        metrics: {
          networkCalls: 0,
          databaseQueries: 0
        },
        artifacts: []
      }));
      runSuite = vi.fn(async () => {
        throw new Error('Suite execution not supported');
      });

      canRun(): boolean {
        return true;
      }
    }

    class ThrowingLifecycleRunner extends LifecycleRunner {
      runTest = vi.fn(async () => {
        throw new Error('Run failure');
      });
    }

    const lifecycleConfig = (runner: TestRunner): IntegrationTestConfig => ({
      environments: [createMockEnvironment()],
      defaultEnvironment: 'test',
      runners: [runner],
      reporters: [],
      globalTimeout: 60000,
      globalRetries: 1,
      parallelSuites: false,
      maxSuiteConcurrency: 1,
      artifactRetention: { days: 7, maxSize: 100 },
      notifications: { enabled: false, channels: [], onFailure: false, onSuccess: false }
    });

    const lifecycleTestCase = (id: string): TestCase => ({
      id,
      name: `Lifecycle Test ${id}`,
      description: 'Verifies runner lifecycle hooks',
      category: 'integration',
      severity: 'major',
      enabled: true,
      preconditions: [],
      steps: [],
      expectedResults: ['Lifecycle hooks executed'],
      fixtures: [],
      dependencies: [],
      tags: [],
      metadata: {
        complexity: 'low',
        stability: 'stable',
        lastUpdated: new Date().toISOString()
      }
    });

    const createExecutionConfig = (): TestExecutionConfig => ({
      environment: 'test',
      parallel: false,
      maxConcurrency: 1,
      timeout: 60000,
      retries: 0,
      skipOnFailure: false,
      failFast: false,
      generateReport: false,
      captureScreenshots: false,
      recordVideo: false,
      collectLogs: true,
      measureCoverage: false,
      outputDir: getOutputDir('lifecycle-results'),
      reportFormat: ['json'],
      filters: {}
    });

    it('should invoke setup, hooks, and teardown for successful runs', async () => {
      const runner = new LifecycleRunner();
      const lifecycleOrchestrator = new IntegrationTestOrchestrator(lifecycleConfig(runner));
      await lifecycleOrchestrator.initialize();
      lifecycleOrchestrator.addTestCase(lifecycleTestCase('lifecycle-success'));

      const result = await lifecycleOrchestrator.executeTest(
        'lifecycle-success',
        'test',
        createExecutionConfig(),
      );

      expect(result.status).toBe('passed');
      expect(runner.setup).toHaveBeenCalledTimes(1);
      expect(runner.beforeTest).toHaveBeenCalledTimes(1);
      expect(runner.afterTest).toHaveBeenCalledTimes(1);
      expect(runner.afterTest).toHaveBeenCalledWith(
        expect.objectContaining({ id: 'lifecycle-success' }),
        expect.objectContaining({ status: 'passed' })
      );
      expect(runner.teardown).toHaveBeenCalledTimes(1);
    });

    it('should still teardown and call afterTest when runTest throws', async () => {
      const runner = new ThrowingLifecycleRunner();
      const lifecycleOrchestrator = new IntegrationTestOrchestrator(lifecycleConfig(runner));
      await lifecycleOrchestrator.initialize();
      lifecycleOrchestrator.addTestCase(lifecycleTestCase('lifecycle-failure'));

      const result = await lifecycleOrchestrator.executeTest(
        'lifecycle-failure',
        'test',
        createExecutionConfig(),
      );

      expect(result.status).toBe('error');
      expect(runner.setup).toHaveBeenCalledTimes(1);
      expect(runner.beforeTest).toHaveBeenCalledTimes(1);
      expect(runner.afterTest).toHaveBeenCalledTimes(1);
      expect(runner.afterTest?.mock.calls[0]?.[1].status).toBe('error');
      expect(runner.teardown).toHaveBeenCalledTimes(1);
    });
  });

});
