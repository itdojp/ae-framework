/**
 * Playwright Integration System for Phase 3.2
 * Provides E2E test automation and intelligent test generation
 */
import { EventEmitter } from 'events';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';
import type { SequentialInferenceEngine } from '../engines/sequential-inference-engine.js';
export interface PlaywrightConfig {
    baseURL: string;
    browserType: 'chromium' | 'firefox' | 'webkit';
    headless: boolean;
    viewport: {
        width: number;
        height: number;
    };
    timeout: number;
    retries: number;
    outputDir: string;
    screenshotMode: 'only-on-failure' | 'off' | 'on';
    videoMode: 'retain-on-failure' | 'off' | 'on';
}
export interface E2ETestCase {
    id: string;
    name: string;
    description: string;
    priority: 'critical' | 'high' | 'medium' | 'low';
    tags: string[];
    steps: TestStep[];
    expectedOutcome: string;
    preconditions: string[];
    testData: Record<string, any>;
    dependencies: string[];
}
export interface TestStep {
    id: string;
    action: TestAction;
    selector?: string;
    value?: string;
    options?: Record<string, any>;
    description: string;
    timeout?: number;
    retry?: boolean;
}
export type TestAction = 'navigate' | 'click' | 'fill' | 'select' | 'wait' | 'assert' | 'screenshot' | 'hover' | 'keyboard' | 'upload' | 'download';
export interface TestGenerationRequest {
    id: string;
    sourceAnalysis: DependencyAnalysisResult;
    targetComponents: string[];
    testTypes: E2ETestType[];
    userFlows: UserFlow[];
    coverage: {
        minCoverage: number;
        includeEdgeCases: boolean;
        includeCriticalPaths: boolean;
    };
    constraints: {
        maxTests: number;
        maxDuration: number;
        browser: PlaywrightConfig['browserType'][];
    };
}
export type E2ETestType = 'smoke' | 'regression' | 'user_journey' | 'integration' | 'critical_path' | 'edge_case';
export interface UserFlow {
    id: string;
    name: string;
    description: string;
    steps: UserFlowStep[];
    priority: 'critical' | 'high' | 'medium' | 'low';
    frequency: 'daily' | 'weekly' | 'monthly' | 'rare';
}
export interface UserFlowStep {
    action: string;
    target: string;
    data?: any;
    expectedResult: string;
}
export interface TestGenerationResult {
    requestId: string;
    generatedTests: E2ETestCase[];
    testSuite: {
        name: string;
        description: string;
        estimatedDuration: number;
        coverage: TestCoverage;
    };
    playwrightConfig: PlaywrightConfig;
    executionPlan: TestExecutionPlan;
    recommendations: TestRecommendation[];
}
export interface TestCoverage {
    componentCoverage: number;
    userFlowCoverage: number;
    criticalPathCoverage: number;
    edgeCaseCoverage: number;
    riskCoverage: {
        high: number;
        medium: number;
        low: number;
    };
}
export interface TestExecutionPlan {
    phases: TestPhase[];
    totalEstimatedTime: number;
    parallelization: {
        maxParallel: number;
        grouping: 'by_component' | 'by_priority' | 'by_dependency';
    };
    retryStrategy: {
        maxRetries: number;
        retryOnFailure: boolean;
        flakyTestHandling: 'retry' | 'skip' | 'quarantine';
    };
}
export interface TestPhase {
    id: string;
    name: string;
    tests: string[];
    dependencies: string[];
    estimatedDuration: number;
    canRunInParallel: boolean;
}
export interface TestRecommendation {
    id: string;
    type: 'performance' | 'coverage' | 'maintenance' | 'optimization';
    priority: 'high' | 'medium' | 'low';
    title: string;
    description: string;
    impact: string;
    effort: 'low' | 'medium' | 'high';
    implementation: string[];
}
export interface TestExecutionResult {
    executionId: string;
    testResults: TestResult[];
    summary: ExecutionSummary;
    failures: TestFailure[];
    performance: PerformanceMetrics;
    artifacts: TestArtifact[];
}
export interface TestResult {
    testId: string;
    status: 'passed' | 'failed' | 'skipped' | 'flaky';
    duration: number;
    browser: string;
    attempts: number;
    error?: string;
    screenshots: string[];
    videos: string[];
    traces: string[];
}
export interface ExecutionSummary {
    total: number;
    passed: number;
    failed: number;
    skipped: number;
    flaky: number;
    duration: number;
    successRate: number;
}
export interface TestFailure {
    testId: string;
    step: string;
    error: string;
    screenshot?: string;
    stackTrace: string;
    reproducible: boolean;
    category: 'environment' | 'flaky' | 'regression' | 'data' | 'timing';
}
export interface PerformanceMetrics {
    avgTestDuration: number;
    slowestTests: Array<{
        testId: string;
        duration: number;
    }>;
    browserPerformance: Record<string, number>;
    memoryUsage: number;
    parallelEfficiency: number;
}
export interface TestArtifact {
    type: 'screenshot' | 'video' | 'trace' | 'report' | 'log';
    path: string;
    testId: string;
    timestamp: Date;
    size: number;
}
export declare class PlaywrightIntegration extends EventEmitter {
    private inferenceEngine;
    private config;
    private activeExecutions;
    private testCache;
    constructor(inferenceEngine: SequentialInferenceEngine, config?: Partial<PlaywrightConfig>);
    /**
     * Generate E2E tests based on dependency analysis and user flows
     */
    generateE2ETests(request: TestGenerationRequest): Promise<TestGenerationResult>;
    /**
     * Execute generated E2E tests
     */
    executeTests(tests: E2ETestCase[], config?: Partial<PlaywrightConfig>): Promise<TestExecutionResult>;
    /**
     * Analyze test coverage based on dependency analysis
     */
    analyzeTestCoverage(tests: E2ETestCase[], dependencyAnalysis: DependencyAnalysisResult): Promise<TestCoverage>;
    /**
     * Generate test recommendations based on analysis
     */
    generateTestRecommendations(tests: E2ETestCase[], dependencyAnalysis: DependencyAnalysisResult, executionPlan: TestExecutionPlan): TestRecommendation[];
    private createDefaultConfig;
    private setupEventHandlers;
    private generateTestsFromAnalysis;
    private createComponentTest;
    private createUserFlowTest;
    private createCircularDependencyTest;
    private createTestSuite;
    private optimizePlaywrightConfig;
    private createExecutionPlan;
    private executeIndividualTest;
    private extractComponentFromSelector;
    private calculateUserFlowCoverage;
    private calculateCriticalPathCoverage;
    private calculateEdgeCaseCoverage;
    private calculateRiskCoverage;
    private calculatePerformanceMetrics;
    private getComponentURL;
    private getComponentSelector;
    private mapFlowActionToTestAction;
    private generateSelectorFromTarget;
    private estimatePhaseTime;
}
