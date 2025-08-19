/**
 * Integration Test Orchestrator
 * Phase 2.3: Central orchestrator for managing and executing integration tests
 */

import { EventEmitter } from 'events';
import { v4 as uuidv4 } from 'uuid';
import { promises as fs } from 'fs';
import { join } from 'path';
import {
  TestCase,
  TestSuite,
  TestFixture,
  TestEnvironment,
  TestExecutionConfig,
  TestExecutionSummary,
  TestResult,
  TestRunner,
  TestReporter,
  IntegrationTestConfig,
  TestDiscovery,
  TestStatus
} from './types.js';

export class IntegrationTestOrchestrator extends EventEmitter {
  private config: IntegrationTestConfig;
  private environments: Map<string, TestEnvironment> = new Map();
  private runners: Map<string, TestRunner> = new Map();
  private reporters: Map<string, TestReporter> = new Map();
  private testCases: Map<string, TestCase> = new Map();
  private testSuites: Map<string, TestSuite> = new Map();
  private testFixtures: Map<string, TestFixture> = new Map();
  private activeExecutions: Map<string, Promise<TestExecutionSummary>> = new Map();

  constructor(config: IntegrationTestConfig) {
    super();
    this.config = config;
    this.setupEnvironments();
    this.setupRunners();
    this.setupReporters();
  }

  /**
   * Initialize the orchestrator
   */
  async initialize(): Promise<void> {
    this.emit('orchestrator_initializing');
    
    // Setup runners
    for (const runner of this.config.runners) {
      this.runners.set(runner.id, runner);
    }

    // Setup reporters
    for (const reporter of this.config.reporters) {
      this.reporters.set(reporter.name, reporter);
    }

    // Setup environments
    for (const env of this.config.environments) {
      this.environments.set(env.name, env);
    }

    this.emit('orchestrator_initialized');
  }

  /**
   * Discover tests from patterns
   */
  async discoverTests(
    discovery: TestDiscovery,
    patterns: string[]
  ): Promise<{ tests: TestCase[]; suites: TestSuite[]; fixtures: TestFixture[] }> {
    this.emit('test_discovery_started', { patterns });

    const [tests, suites, fixtures] = await Promise.all([
      discovery.discoverTests(patterns),
      discovery.discoverSuites(patterns),
      discovery.discoverFixtures(patterns)
    ]);

    // Cache discovered items
    tests.forEach(test => this.testCases.set(test.id, test));
    suites.forEach(suite => this.testSuites.set(suite.id, suite));
    fixtures.forEach(fixture => this.testFixtures.set(fixture.id, fixture));

    this.emit('test_discovery_completed', { 
      testsFound: tests.length,
      suitesFound: suites.length,
      fixturesFound: fixtures.length
    });

    return { tests, suites, fixtures };
  }

  /**
   * Execute a single test case
   */
  async executeTest(
    testId: string,
    environmentName: string,
    config: TestExecutionConfig
  ): Promise<TestResult> {
    const test = this.testCases.get(testId);
    if (!test) {
      throw new Error(`Test not found: ${testId}`);
    }

    const environment = this.environments.get(environmentName);
    if (!environment) {
      throw new Error(`Environment not found: ${environmentName}`);
    }

    const runner = this.findRunner(test);
    if (!runner) {
      throw new Error(`No suitable runner found for test: ${testId}`);
    }

    this.emit('test_started', { testId, environment: environmentName });

    try {
      // Setup fixtures
      await this.setupFixtures(test.fixtures, environment);

      // Execute test
      const result = await runner.runTest(test, environment);

      this.emit('test_completed', { testId, status: result.status, duration: result.duration });
      return result;

    } catch (error) {
      const errorResult: TestResult = {
        id: uuidv4(),
        testId,
        status: 'error',
        startTime: new Date().toISOString(),
        endTime: new Date().toISOString(),
        duration: 0,
        environment: environmentName,
        steps: [],
        error: error instanceof Error ? error.message : String(error),
        stackTrace: error instanceof Error ? error.stack : undefined,
        logs: [`Test execution failed: ${error}`],
        metrics: {
          networkCalls: 0,
          databaseQueries: 0
        }
      };

      this.emit('test_failed', { testId, error: errorResult.error });
      return errorResult;

    } finally {
      // Teardown fixtures
      await this.teardownFixtures(test.fixtures, environment);
    }
  }

  /**
   * Execute a test suite
   */
  async executeSuite(
    suiteId: string,
    environmentName: string,
    config: TestExecutionConfig
  ): Promise<TestExecutionSummary> {
    const executionId = uuidv4();
    const startTime = new Date().toISOString();

    // Check if execution is already in progress
    if (this.activeExecutions.has(suiteId)) {
      throw new Error(`Suite execution already in progress: ${suiteId}`);
    }

    const execution = this.executeSuiteInternal(suiteId, environmentName, config, executionId, startTime);
    this.activeExecutions.set(suiteId, execution);

    try {
      const result = await execution;
      return result;
    } finally {
      this.activeExecutions.delete(suiteId);
    }
  }

  /**
   * Internal suite execution logic
   */
  private async executeSuiteInternal(
    suiteId: string,
    environmentName: string,
    config: TestExecutionConfig,
    executionId: string,
    startTime: string
  ): Promise<TestExecutionSummary> {
    const suite = this.testSuites.get(suiteId);
    if (!suite) {
      throw new Error(`Test suite not found: ${suiteId}`);
    }

    const environment = this.environments.get(environmentName);
    if (!environment) {
      throw new Error(`Environment not found: ${environmentName}`);
    }

    this.emit('suite_started', { suiteId, environment: environmentName, executionId });

    const results: TestResult[] = [];
    const failures: Array<{ testId: string; testName: string; error: string; stackTrace?: string }> = [];

    try {
      // Setup suite fixtures
      await this.setupFixtures(suite.fixtures, environment);

      // Execute setup scripts
      await this.executeSetupScripts(suite.setup, environment);

      // Get tests to execute
      const testsToRun = suite.tests
        .map(testId => this.testCases.get(testId))
        .filter((test): test is TestCase => test !== undefined && test.enabled);

      // Apply filters
      const filteredTests = this.applyFilters(testsToRun, config.filters);

      this.emit('suite_tests_filtered', { 
        suiteId, 
        originalCount: testsToRun.length, 
        filteredCount: filteredTests.length 
      });

      // Execute tests
      if (suite.configuration.parallel && suite.configuration.maxConcurrency > 1) {
        // Parallel execution
        const testResults = await this.executeTestsParallel(
          filteredTests,
          environment,
          config,
          suite.configuration.maxConcurrency
        );
        results.push(...testResults);
      } else {
        // Sequential execution
        for (const test of filteredTests) {
          try {
            const result = await this.executeTest(test.id, environmentName, config);
            results.push(result);

            if (result.status === 'failed') {
              failures.push({
                testId: test.id,
                testName: test.name,
                error: result.error || 'Test failed',
                stackTrace: result.stackTrace
              });

              if (suite.configuration.failFast) {
                this.emit('suite_fail_fast', { suiteId, testId: test.id });
                break;
              }
            }

            if (suite.configuration.skipOnFailure && result.status === 'failed') {
              this.emit('suite_skip_remaining', { suiteId, testId: test.id });
              break;
            }

          } catch (error) {
            const errorMessage = error instanceof Error ? error.message : String(error);
            failures.push({
              testId: test.id,
              testName: test.name,
              error: errorMessage,
              stackTrace: error instanceof Error ? error.stack : undefined
            });
          }
        }
      }

    } finally {
      // Execute teardown scripts
      await this.executeTeardownScripts(suite.teardown, environment);

      // Teardown suite fixtures
      await this.teardownFixtures(suite.fixtures, environment);
    }

    const endTime = new Date().toISOString();
    const duration = new Date(endTime).getTime() - new Date(startTime).getTime();

    // Calculate statistics
    const statistics = this.calculateStatistics(results);

    // Create execution summary
    const summary: TestExecutionSummary = {
      id: executionId,
      startTime,
      endTime,
      duration,
      environment: environmentName,
      configuration: config,
      statistics,
      results,
      failures,
      artifacts: await this.collectArtifacts(config.outputDir, executionId),
      metadata: await this.collectMetadata()
    };

    // Generate reports
    if (config.generateReport) {
      await this.generateReports(summary, config);
    }

    this.emit('suite_completed', { 
      suiteId, 
      executionId, 
      duration, 
      statistics 
    });

    return summary;
  }

  /**
   * Execute tests in parallel
   */
  private async executeTestsParallel(
    tests: TestCase[],
    environment: TestEnvironment,
    config: TestExecutionConfig,
    maxConcurrency: number
  ): Promise<TestResult[]> {
    const results: TestResult[] = [];
    const semaphore = new Array(maxConcurrency).fill(0);

    const executeTest = async (test: TestCase): Promise<TestResult> => {
      // Wait for available slot
      await new Promise<void>(resolve => {
        const check = () => {
          const availableIndex = semaphore.findIndex(slot => slot === 0);
          if (availableIndex !== -1) {
            semaphore[availableIndex] = 1;
            resolve();
          } else {
            setTimeout(check, 100);
          }
        };
        check();
      });

      try {
        return await this.executeTest(test.id, environment.name, config);
      } finally {
        // Release slot
        const usedIndex = semaphore.findIndex(slot => slot === 1);
        if (usedIndex !== -1) {
          semaphore[usedIndex] = 0;
        }
      }
    };

    // Execute all tests
    const promises = tests.map(test => executeTest(test));
    const testResults = await Promise.allSettled(promises);

    // Collect results
    for (const result of testResults) {
      if (result.status === 'fulfilled') {
        results.push(result.value);
      } else {
        // Create error result for failed execution
        results.push({
          id: uuidv4(),
          testId: 'unknown',
          status: 'error',
          startTime: new Date().toISOString(),
          endTime: new Date().toISOString(),
          duration: 0,
          environment: environment.name,
          steps: [],
          error: result.reason?.message || 'Unknown error',
          logs: ['Parallel execution failed'],
          metrics: {
            networkCalls: 0,
            databaseQueries: 0
          }
        });
      }
    }

    return results;
  }

  /**
   * Apply filters to test list
   */
  private applyFilters(
    tests: TestCase[], 
    filters: TestExecutionConfig['filters']
  ): TestCase[] {
    let filtered = tests;

    // Filter by categories
    if (filters.categories && filters.categories.length > 0) {
      filtered = filtered.filter(test => filters.categories!.includes(test.category));
    }

    // Filter by tags
    if (filters.tags && filters.tags.length > 0) {
      filtered = filtered.filter(test => 
        filters.tags!.some(tag => test.tags.includes(tag))
      );
    }

    // Filter by severity
    if (filters.severity && filters.severity.length > 0) {
      filtered = filtered.filter(test => filters.severity!.includes(test.severity));
    }

    // Exclude specific tests
    if (filters.exclude && filters.exclude.length > 0) {
      filtered = filtered.filter(test => !filters.exclude!.includes(test.id));
    }

    return filtered;
  }

  /**
   * Find appropriate runner for test
   */
  private findRunner(test: TestCase): TestRunner | undefined {
    for (const runner of Array.from(this.runners.values())) {
      if (runner.canRun(test)) {
        return runner;
      }
    }
    return undefined;
  }

  /**
   * Setup test fixtures
   */
  private async setupFixtures(fixtureIds: string[], environment: TestEnvironment): Promise<void> {
    for (const fixtureId of fixtureIds) {
      const fixture = this.testFixtures.get(fixtureId);
      if (fixture) {
        await this.executeSetupScripts(fixture.setup, environment);
      }
    }
  }

  /**
   * Teardown test fixtures
   */
  private async teardownFixtures(fixtureIds: string[], environment: TestEnvironment): Promise<void> {
    // Teardown in reverse order
    for (let i = fixtureIds.length - 1; i >= 0; i--) {
      const fixture = this.testFixtures.get(fixtureIds[i]);
      if (fixture) {
        await this.executeTeardownScripts(fixture.teardown, environment);
      }
    }
  }

  /**
   * Execute setup scripts
   */
  private async executeSetupScripts(scripts: string[], environment: TestEnvironment): Promise<void> {
    for (const script of scripts) {
      try {
        // Execute script (implementation depends on script type)
        await this.executeScript(script, environment);
      } catch (error) {
        this.emit('setup_script_failed', { script, error });
        throw error;
      }
    }
  }

  /**
   * Execute teardown scripts
   */
  private async executeTeardownScripts(scripts: string[], environment: TestEnvironment): Promise<void> {
    // Execute in reverse order
    for (let i = scripts.length - 1; i >= 0; i--) {
      try {
        await this.executeScript(scripts[i], environment);
      } catch (error) {
        this.emit('teardown_script_failed', { script: scripts[i], error });
        // Don't throw on teardown failures, just log them
      }
    }
  }

  /**
   * Execute a script
   */
  private async executeScript(script: string, environment: TestEnvironment): Promise<void> {
    // This is a simplified implementation
    // In practice, you'd have different script executors based on script type
    if (script.startsWith('sql:')) {
      // Execute SQL script
      await this.executeSQLScript(script.substring(4), environment);
    } else if (script.startsWith('api:')) {
      // Execute API call
      await this.executeAPIScript(script.substring(4), environment);
    } else if (script.startsWith('shell:')) {
      // Execute shell command
      await this.executeShellScript(script.substring(6), environment);
    } else {
      // Default: treat as shell command
      await this.executeShellScript(script, environment);
    }
  }

  /**
   * Execute SQL script
   */
  private async executeSQLScript(script: string, environment: TestEnvironment): Promise<void> {
    // Implementation would depend on database connection
    console.log(`Executing SQL: ${script} in ${environment.name}`);
  }

  /**
   * Execute API script
   */
  private async executeAPIScript(script: string, environment: TestEnvironment): Promise<void> {
    // Implementation would make HTTP requests
    console.log(`Executing API call: ${script} in ${environment.name}`);
  }

  /**
   * Execute shell script
   */
  private async executeShellScript(script: string, environment: TestEnvironment): Promise<void> {
    // Implementation would execute shell commands
    console.log(`Executing shell: ${script} in ${environment.name}`);
  }

  /**
   * Calculate test statistics
   */
  private calculateStatistics(results: TestResult[]) {
    const total = results.length;
    const passed = results.filter(r => r.status === 'passed').length;
    const failed = results.filter(r => r.status === 'failed').length;
    const skipped = results.filter(r => r.status === 'skipped').length;
    const timeout = results.filter(r => r.status === 'timeout').length;
    const error = results.filter(r => r.status === 'error').length;
    const passRate = total > 0 ? (passed / total) * 100 : 0;

    return {
      total,
      passed,
      failed,
      skipped,
      timeout,
      error,
      passRate
    };
  }

  /**
   * Collect test artifacts
   */
  private async collectArtifacts(outputDir: string, executionId: string): Promise<Array<{
    name: string;
    path: string;
    size: number;
  }>> {
    const artifacts: Array<{ name: string; path: string; size: number }> = [];
    const artifactDir = join(outputDir, executionId);

    try {
      const files = await fs.readdir(artifactDir);
      for (const file of files) {
        const filePath = join(artifactDir, file);
        const stats = await fs.stat(filePath);
        artifacts.push({
          name: file,
          path: filePath,
          size: stats.size
        });
      }
    } catch (error) {
      // Directory might not exist yet
    }

    return artifacts;
  }

  /**
   * Collect metadata
   */
  private async collectMetadata(): Promise<Record<string, any>> {
    return {
      nodeVersion: process.version,
      platform: process.platform,
      timestamp: new Date().toISOString()
    };
  }

  /**
   * Generate test reports
   */
  private async generateReports(
    summary: TestExecutionSummary, 
    config: TestExecutionConfig
  ): Promise<void> {
    const outputDir = config.outputDir;
    await fs.mkdir(outputDir, { recursive: true });

    for (const format of config.reportFormat) {
      const reporter = Array.from(this.reporters.values())
        .find(r => r.format === format);

      if (reporter) {
        try {
          const content = await reporter.generateReport(summary);
          const fileName = `test-report-${summary.id}.${format}`;
          const filePath = join(outputDir, fileName);
          await reporter.saveReport(content, filePath);

          this.emit('report_generated', { format, filePath });
        } catch (error) {
          this.emit('report_generation_failed', { format, error });
        }
      }
    }
  }

  /**
   * Setup environments
   */
  private setupEnvironments(): void {
    for (const env of this.config.environments) {
      this.environments.set(env.name, env);
    }
  }

  /**
   * Setup runners
   */
  private setupRunners(): void {
    for (const runner of this.config.runners) {
      this.runners.set(runner.id, runner);
    }
  }

  /**
   * Setup reporters
   */
  private setupReporters(): void {
    for (const reporter of this.config.reporters) {
      this.reporters.set(reporter.name, reporter);
    }
  }

  /**
   * Get execution status
   */
  getExecutionStatus(suiteId: string): 'idle' | 'running' | 'unknown' {
    if (this.activeExecutions.has(suiteId)) {
      return 'running';
    }
    return 'idle';
  }

  /**
   * Cancel execution
   */
  async cancelExecution(suiteId: string): Promise<boolean> {
    if (this.activeExecutions.has(suiteId)) {
      // In a real implementation, you'd need to handle cancellation properly
      this.emit('execution_cancelled', { suiteId });
      return true;
    }
    return false;
  }

  /**
   * Get available environments
   */
  getEnvironments(): TestEnvironment[] {
    return Array.from(this.environments.values());
  }

  /**
   * Get available runners
   */
  getRunners(): TestRunner[] {
    return Array.from(this.runners.values());
  }

  /**
   * Get test cases
   */
  getTestCases(): TestCase[] {
    return Array.from(this.testCases.values());
  }

  /**
   * Get test suites
   */
  getTestSuites(): TestSuite[] {
    return Array.from(this.testSuites.values());
  }

  /**
   * Add test case
   */
  addTestCase(test: TestCase): void {
    this.testCases.set(test.id, test);
    this.emit('test_case_added', { testId: test.id });
  }

  /**
   * Add test suite
   */
  addTestSuite(suite: TestSuite): void {
    this.testSuites.set(suite.id, suite);
    this.emit('test_suite_added', { suiteId: suite.id });
  }

  /**
   * Add test fixture
   */
  addTestFixture(fixture: TestFixture): void {
    this.testFixtures.set(fixture.id, fixture);
    this.emit('test_fixture_added', { fixtureId: fixture.id });
  }
}