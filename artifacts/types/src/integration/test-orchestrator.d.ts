/**
 * Integration Test Orchestrator
 * Phase 2.3: Central orchestrator for managing and executing integration tests
 */
import { EventEmitter } from 'events';
import { TestCase, TestSuite, TestFixture, TestEnvironment, TestExecutionConfig, TestExecutionSummary, TestResult, TestRunner, IntegrationTestConfig, TestDiscovery } from './types.js';
export declare class IntegrationTestOrchestrator extends EventEmitter {
    private config;
    private environments;
    private runners;
    private reporters;
    private testCases;
    private testSuites;
    private testFixtures;
    private activeExecutions;
    constructor(config: IntegrationTestConfig);
    /**
     * Initialize the orchestrator
     */
    initialize(): Promise<void>;
    /**
     * Discover tests from patterns
     */
    discoverTests(discovery: TestDiscovery, patterns: string[]): Promise<{
        tests: TestCase[];
        suites: TestSuite[];
        fixtures: TestFixture[];
    }>;
    /**
     * Execute a single test case
     */
    executeTest(testId: string, environmentName: string, config: TestExecutionConfig): Promise<TestResult>;
    /**
     * Execute a test suite
     */
    executeSuite(suiteId: string, environmentName: string, config: TestExecutionConfig): Promise<TestExecutionSummary>;
    /**
     * Internal suite execution logic
     */
    private executeSuiteInternal;
    /**
     * Execute tests in parallel
     */
    private executeTestsParallel;
    /**
     * Apply filters to test list
     */
    private applyFilters;
    /**
     * Find appropriate runner for test
     */
    private findRunner;
    /**
     * Setup test fixtures
     */
    private setupFixtures;
    /**
     * Teardown test fixtures
     */
    private teardownFixtures;
    /**
     * Execute setup scripts
     */
    private executeSetupScripts;
    /**
     * Execute teardown scripts
     */
    private executeTeardownScripts;
    /**
     * Execute a script
     */
    private executeScript;
    /**
     * Execute SQL script
     */
    private executeSQLScript;
    /**
     * Execute API script
     */
    private executeAPIScript;
    /**
     * Execute shell script
     */
    private executeShellScript;
    /**
     * Calculate test statistics
     */
    private calculateStatistics;
    /**
     * Collect test artifacts
     */
    private collectArtifacts;
    /**
     * Collect metadata
     */
    private collectMetadata;
    /**
     * Generate test reports
     */
    private generateReports;
    /**
     * Setup environments
     */
    private setupEnvironments;
    /**
     * Setup runners
     */
    private setupRunners;
    /**
     * Setup reporters
     */
    private setupReporters;
    /**
     * Get execution status
     */
    getExecutionStatus(suiteId: string): 'idle' | 'running' | 'unknown';
    /**
     * Cancel execution
     */
    cancelExecution(suiteId: string): Promise<boolean>;
    /**
     * Get available environments
     */
    getEnvironments(): TestEnvironment[];
    /**
     * Get available runners
     */
    getRunners(): TestRunner[];
    /**
     * Get test cases
     */
    getTestCases(): TestCase[];
    /**
     * Get test suites
     */
    getTestSuites(): TestSuite[];
    /**
     * Add test case
     */
    addTestCase(test: TestCase): void;
    /**
     * Add test suite
     */
    addTestSuite(suite: TestSuite): void;
    /**
     * Add test fixture
     */
    addTestFixture(fixture: TestFixture): void;
}
