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

export type TestAction = 
  | 'navigate'
  | 'click'
  | 'fill'
  | 'select'
  | 'wait'
  | 'assert'
  | 'screenshot'
  | 'hover'
  | 'keyboard'
  | 'upload'
  | 'download';

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

export type E2ETestType = 
  | 'smoke'
  | 'regression'
  | 'user_journey'
  | 'integration'
  | 'critical_path'
  | 'edge_case';

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
  slowestTests: Array<{ testId: string; duration: number }>;
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

export class PlaywrightIntegration extends EventEmitter {
  private inferenceEngine: SequentialInferenceEngine;
  private config: PlaywrightConfig;
  private activeExecutions = new Map<string, TestExecutionResult>();
  private testCache = new Map<string, E2ETestCase[]>();

  constructor(
    inferenceEngine: SequentialInferenceEngine,
    config: Partial<PlaywrightConfig> = {}
  ) {
    super();
    this.inferenceEngine = inferenceEngine;
    this.config = this.createDefaultConfig(config);
    this.setupEventHandlers();
  }

  /**
   * Generate E2E tests based on dependency analysis and user flows
   */
  async generateE2ETests(request: TestGenerationRequest): Promise<TestGenerationResult> {
    this.emit('testGenerationStarted', request);

    try {
      // Use inference engine to analyze test generation requirements
      const analysisQuery = {
        id: `test-gen-${request.id}`,
        description: 'Generate comprehensive E2E test suite',
        constraints: [
          {
            type: 'resource' as const,
            condition: 'maxDepth <= 10',
            severity: 'warning' as const
          },
          {
            type: 'temporal' as const,
            condition: 'timeout <= 60000',
            severity: 'error' as const
          }
        ],
        context: {
          sourceAnalysis: request.sourceAnalysis,
          userFlows: request.userFlows,
          constraints: request.constraints
        },
        priority: 'high' as const
      };

      const inferenceResult = await this.inferenceEngine.processComplexQuery(analysisQuery);

      // Generate tests based on components and user flows
      const generatedTests = await this.generateTestsFromAnalysis(request);

      // Create test suite configuration
      const testSuite = this.createTestSuite(generatedTests, request);

      // Generate Playwright configuration
      const playwrightConfig = this.optimizePlaywrightConfig(request, generatedTests);

      // Create execution plan
      const executionPlan = this.createExecutionPlan(generatedTests, request);

      // Generate recommendations
      const recommendations = this.generateTestRecommendations(
        generatedTests, 
        request.sourceAnalysis,
        executionPlan
      );

      const result: TestGenerationResult = {
        requestId: request.id,
        generatedTests,
        testSuite,
        playwrightConfig,
        executionPlan,
        recommendations
      };

      // Cache the generated tests
      this.testCache.set(request.id, generatedTests);

      this.emit('testGenerationCompleted', { request, result });
      return result;

    } catch (error) {
      this.emit('testGenerationError', { request, error });
      throw error;
    }
  }

  /**
   * Execute generated E2E tests
   */
  async executeTests(
    tests: E2ETestCase[], 
    config?: Partial<PlaywrightConfig>
  ): Promise<TestExecutionResult> {
    const executionId = `exec-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;
    const executionConfig = { ...this.config, ...config };

    this.emit('testExecutionStarted', { executionId, tests, config: executionConfig });

    try {
      const execution: TestExecutionResult = {
        executionId,
        testResults: [],
        summary: {
          total: tests.length,
          passed: 0,
          failed: 0,
          skipped: 0,
          flaky: 0,
          duration: 0,
          successRate: 0
        },
        failures: [],
        performance: {
          avgTestDuration: 0,
          slowestTests: [],
          browserPerformance: {},
          memoryUsage: 0,
          parallelEfficiency: 0
        },
        artifacts: []
      };

      this.activeExecutions.set(executionId, execution);

      // Execute tests (simulated implementation - would use actual Playwright)
      for (const test of tests) {
        const testResult = await this.executeIndividualTest(test, executionConfig);
        execution.testResults.push(testResult);
        
        if (testResult.status === 'passed') execution.summary.passed++;
        else if (testResult.status === 'failed') execution.summary.failed++;
        else if (testResult.status === 'skipped') execution.summary.skipped++;
        else if (testResult.status === 'flaky') execution.summary.flaky++;

        execution.summary.duration += testResult.duration;
      }

      // Calculate final metrics
      execution.summary.successRate = execution.summary.passed / execution.summary.total;
      execution.performance = this.calculatePerformanceMetrics(execution.testResults);

      this.emit('testExecutionCompleted', execution);
      return execution;

    } catch (error) {
      this.emit('testExecutionError', { executionId, error });
      throw error;
    } finally {
      this.activeExecutions.delete(executionId);
    }
  }

  /**
   * Analyze test coverage based on dependency analysis
   */
  async analyzeTestCoverage(
    tests: E2ETestCase[], 
    dependencyAnalysis: DependencyAnalysisResult
  ): Promise<TestCoverage> {
    const totalComponents = dependencyAnalysis.nodes.length;

    // Calculate component coverage
    const testedComponents = new Set<string>();
    tests.forEach(test => {
      test.steps.forEach(step => {
        if (step.selector) {
          testedComponents.add(this.extractComponentFromSelector(step.selector));
        }
      });
    });

    const componentCoverage = testedComponents.size / totalComponents;

    // Calculate risk coverage
    const highRiskFactors = dependencyAnalysis.riskAssessment.riskFactors.filter(
      rf => rf.severity === 'critical' || rf.severity === 'high'
    );
    const mediumRiskFactors = dependencyAnalysis.riskAssessment.riskFactors.filter(
      rf => rf.severity === 'medium'
    );
    const lowRiskFactors = dependencyAnalysis.riskAssessment.riskFactors.filter(
      rf => rf.severity === 'low'
    );

    return {
      componentCoverage,
      userFlowCoverage: this.calculateUserFlowCoverage(tests),
      criticalPathCoverage: this.calculateCriticalPathCoverage(tests, dependencyAnalysis),
      edgeCaseCoverage: this.calculateEdgeCaseCoverage(tests),
      riskCoverage: {
        high: this.calculateRiskCoverage(tests, highRiskFactors),
        medium: this.calculateRiskCoverage(tests, mediumRiskFactors),
        low: this.calculateRiskCoverage(tests, lowRiskFactors)
      }
    };
  }

  /**
   * Generate test recommendations based on analysis
   */
  generateTestRecommendations(
    tests: E2ETestCase[],
    dependencyAnalysis: DependencyAnalysisResult,
    executionPlan: TestExecutionPlan
  ): TestRecommendation[] {
    const recommendations: TestRecommendation[] = [];

    // Coverage recommendations
    if (tests.length < 10) {
      recommendations.push({
        id: 'increase-coverage',
        type: 'coverage',
        priority: 'high',
        title: 'Increase Test Coverage',
        description: 'Current test suite has limited coverage. Consider adding more test cases.',
        impact: 'Improved confidence in system reliability',
        effort: 'medium',
        implementation: [
          'Add tests for critical user journeys',
          'Include edge case scenarios',
          'Test error handling paths'
        ]
      });
    }

    // Performance recommendations
    if (executionPlan.totalEstimatedTime > 1800000) { // 30 minutes
      recommendations.push({
        id: 'optimize-performance',
        type: 'performance',
        priority: 'medium',
        title: 'Optimize Test Execution Time',
        description: 'Test suite execution time is high. Consider optimization strategies.',
        impact: 'Faster feedback cycles',
        effort: 'medium',
        implementation: [
          'Increase parallelization',
          'Optimize test data setup',
          'Use shared browser contexts'
        ]
      });
    }

    // Maintenance recommendations
    const complexTests = tests.filter(t => t.steps.length > 20);
    if (complexTests.length > 0) {
      recommendations.push({
        id: 'simplify-tests',
        type: 'maintenance',
        priority: 'medium',
        title: 'Simplify Complex Tests',
        description: `${complexTests.length} tests have high complexity. Consider breaking them down.`,
        impact: 'Improved maintainability and reliability',
        effort: 'high',
        implementation: [
          'Break complex tests into smaller scenarios',
          'Use page object patterns',
          'Extract common workflows'
        ]
      });
    }

    return recommendations;
  }

  // Private helper methods
  private createDefaultConfig(overrides: Partial<PlaywrightConfig>): PlaywrightConfig {
    return {
      baseURL: 'http://localhost:3000',
      browserType: 'chromium',
      headless: true,
      viewport: { width: 1280, height: 720 },
      timeout: 30000,
      retries: 2,
      outputDir: './test-results',
      screenshotMode: 'only-on-failure',
      videoMode: 'retain-on-failure',
      ...overrides
    };
  }

  private setupEventHandlers(): void {
    this.on('testGenerationStarted', (request) => {
      console.log(`🎭 Test generation started: ${request.id}`);
    });

    this.on('testGenerationCompleted', ({ result }) => {
      console.log(`✅ Generated ${result.generatedTests.length} E2E tests`);
    });

    this.on('testExecutionStarted', ({ executionId, tests }) => {
      console.log(`🚀 Test execution started: ${executionId} (${tests.length} tests)`);
    });

    this.on('testExecutionCompleted', (result) => {
      console.log(`🎯 Test execution completed: ${result.summary.passed}/${result.summary.total} passed`);
    });
  }

  private async generateTestsFromAnalysis(request: TestGenerationRequest): Promise<E2ETestCase[]> {
    const tests: E2ETestCase[] = [];

    // Generate tests for critical components
    const criticalComponents = request.sourceAnalysis.nodes.filter(
      node => node.metadata['importance'] === 'critical'
    );

    for (const component of criticalComponents.slice(0, 5)) { // Limit to top 5
      const test = this.createComponentTest(component, request);
      tests.push(test);
    }

    // Generate tests for user flows
    for (const userFlow of request.userFlows) {
      const test = this.createUserFlowTest(userFlow, request);
      tests.push(test);
    }

    // Generate tests for circular dependencies (if any)
    if (request.sourceAnalysis.circularDependencies.length > 0) {
      const circularDepTest = this.createCircularDependencyTest(
        request.sourceAnalysis.circularDependencies[0],
        request
      );
      tests.push(circularDepTest);
    }

    return tests;
  }

  private createComponentTest(component: any, request: TestGenerationRequest): E2ETestCase {
    return {
      id: `test-${component.id}`,
      name: `Test ${component.name} Component`,
      description: `E2E test for ${component.name} component functionality`,
      priority: component.metadata.importance === 'critical' ? 'critical' : 'high',
      tags: ['component', 'automated', component.type],
      steps: [
        {
          id: 'navigate',
          action: 'navigate',
          description: 'Navigate to component page',
          value: this.getComponentURL(component)
        },
        {
          id: 'verify-load',
          action: 'wait',
          selector: this.getComponentSelector(component),
          description: 'Wait for component to load',
          timeout: 5000
        },
        {
          id: 'interact',
          action: 'click',
          selector: this.getComponentSelector(component),
          description: 'Interact with component'
        },
        {
          id: 'verify-response',
          action: 'assert',
          description: 'Verify component responds correctly',
          value: 'visible'
        }
      ],
      expectedOutcome: `${component.name} component functions correctly`,
      preconditions: ['Application is running', 'User is authenticated'],
      testData: { componentId: component.id },
      dependencies: component.dependencies.slice(0, 3)
    };
  }

  private createUserFlowTest(userFlow: UserFlow, request: TestGenerationRequest): E2ETestCase {
    const steps: TestStep[] = userFlow.steps.map((flowStep, index) => ({
      id: `step-${index}`,
      action: this.mapFlowActionToTestAction(flowStep.action),
      selector: this.generateSelectorFromTarget(flowStep.target),
      ...(flowStep.data ? { value: String(flowStep.data) } : {}),
      description: `${flowStep.action} on ${flowStep.target}`
    }));

    return {
      id: `test-${userFlow.id}`,
      name: `User Flow: ${userFlow.name}`,
      description: userFlow.description,
      priority: userFlow.priority,
      tags: ['user-flow', 'e2e', userFlow.frequency],
      steps,
      expectedOutcome: userFlow.steps[userFlow.steps.length - 1]?.expectedResult || 'Test flow completes successfully',
      preconditions: ['User is authenticated', 'Application is in initial state'],
      testData: { flowId: userFlow.id },
      dependencies: []
    };
  }

  private createCircularDependencyTest(
    circularDep: any,
    request: TestGenerationRequest
  ): E2ETestCase {
    return {
      id: `test-circular-${circularDep.id}`,
      name: 'Circular Dependency Impact Test',
      description: `Test system behavior with circular dependency: ${circularDep.description}`,
      priority: 'high',
      tags: ['circular-dependency', 'risk', 'regression'],
      steps: [
        {
          id: 'navigate',
          action: 'navigate',
          description: 'Navigate to affected component',
          value: '/affected-component'
        },
        {
          id: 'trigger-dependency',
          action: 'click',
          selector: '[data-testid="dependency-trigger"]',
          description: 'Trigger circular dependency scenario'
        },
        {
          id: 'verify-no-loop',
          action: 'wait',
          description: 'Verify no infinite loop occurs',
          timeout: 10000
        },
        {
          id: 'assert-stability',
          action: 'assert',
          description: 'Assert system remains stable',
          value: 'visible'
        }
      ],
      expectedOutcome: 'System handles circular dependency gracefully',
      preconditions: ['Circular dependency exists in code'],
      testData: { circularDepId: circularDep.id },
      dependencies: circularDep.cycle
    };
  }

  private createTestSuite(tests: E2ETestCase[], request: TestGenerationRequest) {
    const totalDuration = tests.reduce((sum, test) => 
      sum + (test.steps.length * 2000), 0 // Estimate 2s per step
    );

    return {
      name: `E2E Test Suite - ${request.id}`,
      description: 'Auto-generated comprehensive E2E test suite',
      estimatedDuration: totalDuration,
      coverage: {
        componentCoverage: 0.85, // Will be calculated properly
        userFlowCoverage: 0.90,
        criticalPathCoverage: 0.75,
        edgeCaseCoverage: 0.60,
        riskCoverage: { high: 0.80, medium: 0.70, low: 0.50 }
      }
    };
  }

  private optimizePlaywrightConfig(
    request: TestGenerationRequest,
    tests: E2ETestCase[]
  ): PlaywrightConfig {
    const config = { ...this.config };

    // Optimize based on test characteristics
    if (tests.length > 20) {
      config.retries = 1; // Reduce retries for large test suites
    }

    if (request.constraints.browser.length === 1) {
      config.browserType = request.constraints.browser[0] || 'chromium';
    }

    // Adjust timeout based on test complexity
    const avgStepsPerTest = tests.reduce((sum, test) => sum + test.steps.length, 0) / tests.length;
    if (avgStepsPerTest > 15) {
      config.timeout = 60000; // Increase timeout for complex tests
    }

    return config;
  }

  private createExecutionPlan(
    tests: E2ETestCase[],
    request: TestGenerationRequest
  ): TestExecutionPlan {
    // Group tests by priority and dependencies
    const criticalTests = tests.filter(t => t.priority === 'critical');
    const highTests = tests.filter(t => t.priority === 'high');
    const mediumTests = tests.filter(t => t.priority === 'medium');
    const lowTests = tests.filter(t => t.priority === 'low');

    const phases: TestPhase[] = [];

    if (criticalTests.length > 0) {
      phases.push({
        id: 'critical-phase',
        name: 'Critical Tests',
        tests: criticalTests.map(t => t.id),
        dependencies: [],
        estimatedDuration: this.estimatePhaseTime(criticalTests),
        canRunInParallel: false
      });
    }

    if (highTests.length > 0) {
      phases.push({
        id: 'high-priority-phase',
        name: 'High Priority Tests',
        tests: highTests.map(t => t.id),
        dependencies: criticalTests.length > 0 ? ['critical-phase'] : [],
        estimatedDuration: this.estimatePhaseTime(highTests),
        canRunInParallel: true
      });
    }

    if (mediumTests.length > 0 || lowTests.length > 0) {
      phases.push({
        id: 'standard-phase',
        name: 'Standard Tests',
        tests: [...mediumTests, ...lowTests].map(t => t.id),
        dependencies: phases.map(p => p.id),
        estimatedDuration: this.estimatePhaseTime([...mediumTests, ...lowTests]),
        canRunInParallel: true
      });
    }

    return {
      phases,
      totalEstimatedTime: phases.reduce((sum, phase) => sum + phase.estimatedDuration, 0),
      parallelization: {
        maxParallel: Math.min(4, tests.length),
        grouping: 'by_priority'
      },
      retryStrategy: {
        maxRetries: 2,
        retryOnFailure: true,
        flakyTestHandling: 'retry'
      }
    };
  }

  private async executeIndividualTest(
    test: E2ETestCase,
    config: PlaywrightConfig
  ): Promise<TestResult> {
    // Simulated test execution - in real implementation would use Playwright
    const startTime = Date.now();
    
    try {
      // Simulate test execution time based on steps
      const executionTime = test.steps.length * 1000 + Math.random() * 2000;
      await new Promise(resolve => setTimeout(resolve, executionTime));

      // Simulate success/failure based on test characteristics
      const successProbability = test.priority === 'critical' ? 0.95 : 0.85;
      const success = Math.random() < successProbability;

      return {
        testId: test.id,
        status: success ? 'passed' : 'failed',
        duration: Date.now() - startTime,
        browser: config.browserType,
        attempts: success ? 1 : 2,
        ...(success ? {} : { error: 'Simulated test failure' }),
        screenshots: success ? [] : [`${test.id}-failure.png`],
        videos: [],
        traces: []
      };
    } catch (error) {
      return {
        testId: test.id,
        status: 'failed',
        duration: Date.now() - startTime,
        browser: config.browserType,
        attempts: 1,
        error: (error as Error).message,
        screenshots: [`${test.id}-error.png`],
        videos: [],
        traces: []
      };
    }
  }

  // Additional helper methods
  private extractComponentFromSelector(selector: string): string {
    // Extract component identifier from CSS selector
    const match = selector.match(/\[data-component="([^"]+)"\]/);
    return match?.[1] || 'unknown';
  }

  private calculateUserFlowCoverage(tests: E2ETestCase[]): number {
    const userFlowTests = tests.filter(t => t.tags.includes('user-flow'));
    return userFlowTests.length / Math.max(tests.length, 1);
  }

  private calculateCriticalPathCoverage(
    tests: E2ETestCase[],
    dependencyAnalysis: DependencyAnalysisResult
  ): number {
    const criticalNodes = dependencyAnalysis.nodes.filter(
      n => n.metadata['importance'] === 'critical'
    );
    const testedCriticalComponents = new Set<string>();
    
    tests.forEach(test => {
      if (test.priority === 'critical') {
        test.dependencies.forEach(dep => testedCriticalComponents.add(dep));
      }
    });

    return testedCriticalComponents.size / Math.max(criticalNodes.length, 1);
  }

  private calculateEdgeCaseCoverage(tests: E2ETestCase[]): number {
    const edgeCaseTests = tests.filter(t => 
      t.tags.includes('edge-case') || t.description.toLowerCase().includes('edge')
    );
    return edgeCaseTests.length / Math.max(tests.length * 0.2, 1); // Expect 20% edge cases
  }

  private calculateRiskCoverage(tests: E2ETestCase[], riskFactors: any[]): number {
    if (riskFactors.length === 0) return 1.0;
    
    const riskTests = tests.filter(t => t.tags.includes('risk'));
    return riskTests.length / riskFactors.length;
  }

  private calculatePerformanceMetrics(testResults: TestResult[]): PerformanceMetrics {
    const durations = testResults.map(r => r.duration);
    const avgDuration = durations.reduce((sum, d) => sum + d, 0) / durations.length;
    
    const slowestTests = testResults
      .sort((a, b) => b.duration - a.duration)
      .slice(0, 5)
      .map(r => ({ testId: r.testId, duration: r.duration }));

    return {
      avgTestDuration: avgDuration,
      slowestTests,
      browserPerformance: { chromium: avgDuration },
      memoryUsage: 0, // Would be measured in real implementation
      parallelEfficiency: 0.8 // Estimated
    };
  }

  private getComponentURL(component: any): string {
    return `/${component.name.toLowerCase().replace(/\s+/g, '-')}`;
  }

  private getComponentSelector(component: any): string {
    return `[data-testid="${component.id}"]`;
  }

  private mapFlowActionToTestAction(action: string): TestAction {
    const actionMap: Record<string, TestAction> = {
      'click': 'click',
      'fill': 'fill',
      'navigate': 'navigate',
      'wait': 'wait',
      'select': 'select',
      'type': 'fill',
      'submit': 'click'
    };
    return actionMap[action.toLowerCase()] || 'click';
  }

  private generateSelectorFromTarget(target: string): string {
    return `[data-testid="${target.toLowerCase().replace(/\s+/g, '-')}"]`;
  }

  private estimatePhaseTime(tests: E2ETestCase[]): number {
    return tests.reduce((sum, test) => sum + (test.steps.length * 2000), 0);
  }
}
