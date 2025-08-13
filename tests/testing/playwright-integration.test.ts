/**
 * Test Suite for Playwright Integration System (Phase 3.2)
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { PlaywrightIntegration, type TestGenerationRequest, type E2ETestCase, type PlaywrightConfig } from '../../src/testing/playwright-integration.js';
import type { SequentialInferenceEngine } from '../../src/engines/sequential-inference-engine.js';
import type { DependencyAnalysisResult } from '../../src/analysis/dependency-analyzer.js';

// Mock SequentialInferenceEngine
const mockInferenceEngine: SequentialInferenceEngine = {
  processComplexQuery: vi.fn().mockResolvedValue({
    id: 'test-query',
    status: 'completed',
    result: { analysis: 'mock analysis' },
    reasoning: [],
    confidence: 0.9
  }),
  analyzeImpact: vi.fn(),
  evaluateEvidence: vi.fn(),
  reasonStep: vi.fn(),
  synthesizeResults: vi.fn(),
  on: vi.fn(),
  emit: vi.fn()
} as any;

const mockDependencyAnalysis: DependencyAnalysisResult = {
  id: 'test-analysis',
  timestamp: new Date(),
  graph: {
    nodes: [
      { id: 'comp1', name: 'Component1', type: 'component', dependencies: [], metadata: { importance: 'critical', complexity: 5 } },
      { id: 'comp2', name: 'Component2', type: 'component', dependencies: ['comp1'], metadata: { importance: 'high', complexity: 3 } }
    ],
    edges: [{ from: 'comp2', to: 'comp1', type: 'dependency', weight: 1 }]
  },
  nodes: [
    { id: 'comp1', name: 'Component1', type: 'component', dependencies: [], metadata: { importance: 'critical', complexity: 5 } },
    { id: 'comp2', name: 'Component2', type: 'component', dependencies: ['comp1'], metadata: { importance: 'high', complexity: 3 } }
  ],
  circularDependencies: [],
  criticalPaths: [{ id: 'path1', nodes: ['comp1', 'comp2'], weight: 2, description: 'Critical path' }],
  riskAssessment: {
    overallRisk: 'medium',
    riskFactors: [
      { id: 'rf1', type: 'complexity', severity: 'medium', affectedNodes: ['comp1'], description: 'Complex component', mitigation: 'Review code' }
    ],
    recommendations: []
  },
  optimizations: []
};

describe('PlaywrightIntegration', () => {
  let playwrightIntegration: PlaywrightIntegration;

  beforeEach(() => {
    playwrightIntegration = new PlaywrightIntegration(mockInferenceEngine);
  });

  describe('constructor', () => {
    it('should initialize with default config', () => {
      expect(playwrightIntegration).toBeInstanceOf(PlaywrightIntegration);
    });

    it('should accept custom config overrides', () => {
      const customConfig: Partial<PlaywrightConfig> = {
        baseURL: 'http://localhost:8080',
        browserType: 'firefox',
        headless: false
      };
      const integration = new PlaywrightIntegration(mockInferenceEngine, customConfig);
      expect(integration).toBeInstanceOf(PlaywrightIntegration);
    });
  });

  describe('generateE2ETests', () => {
    const testRequest: TestGenerationRequest = {
      id: 'test-req-1',
      sourceAnalysis: mockDependencyAnalysis,
      targetComponents: ['comp1', 'comp2'],
      testTypes: ['smoke', 'regression', 'user_journey'],
      userFlows: [
        {
          id: 'flow1',
          name: 'User Login',
          description: 'User login flow',
          steps: [
            { action: 'navigate', target: 'login-page', expectedResult: 'Page loads' },
            { action: 'fill', target: 'username', data: 'testuser', expectedResult: 'Username filled' },
            { action: 'fill', target: 'password', data: 'password', expectedResult: 'Password filled' },
            { action: 'click', target: 'login-button', expectedResult: 'User logged in' }
          ],
          priority: 'critical',
          frequency: 'daily'
        }
      ],
      coverage: {
        minCoverage: 0.8,
        includeEdgeCases: true,
        includeCriticalPaths: true
      },
      constraints: {
        maxTests: 20,
        maxDuration: 1800000, // 30 minutes
        browser: ['chromium']
      }
    };

    it('should generate comprehensive test suite', async () => {
      const result = await playwrightIntegration.generateE2ETests(testRequest);

      expect(result).toMatchObject({
        requestId: 'test-req-1',
        generatedTests: expect.any(Array),
        testSuite: expect.objectContaining({
          name: expect.stringContaining('E2E Test Suite'),
          description: expect.any(String),
          estimatedDuration: expect.any(Number)
        }),
        playwrightConfig: expect.any(Object),
        executionPlan: expect.any(Object),
        recommendations: expect.any(Array)
      });

      expect(result.generatedTests.length).toBeGreaterThan(0);
    });

    it('should generate tests for critical components', async () => {
      const result = await playwrightIntegration.generateE2ETests(testRequest);
      
      const componentTests = result.generatedTests.filter(test => 
        test.tags.includes('component')
      );
      expect(componentTests.length).toBeGreaterThan(0);
    });

    it('should generate tests for user flows', async () => {
      const result = await playwrightIntegration.generateE2ETests(testRequest);
      
      const userFlowTests = result.generatedTests.filter(test => 
        test.tags.includes('user-flow')
      );
      expect(userFlowTests.length).toBe(1); // One user flow in request
    });

    it('should respect test constraints', async () => {
      const result = await playwrightIntegration.generateE2ETests(testRequest);
      
      expect(result.generatedTests.length).toBeLessThanOrEqual(testRequest.constraints.maxTests);
      expect(result.testSuite.estimatedDuration).toBeLessThanOrEqual(testRequest.constraints.maxDuration);
    });

    it('should generate execution plan with phases', async () => {
      const result = await playwrightIntegration.generateE2ETests(testRequest);
      
      expect(result.executionPlan.phases.length).toBeGreaterThan(0);
      expect(result.executionPlan.totalEstimatedTime).toBeGreaterThan(0);
      expect(result.executionPlan.parallelization).toMatchObject({
        maxParallel: expect.any(Number),
        grouping: expect.stringMatching(/by_(component|priority|dependency)/)
      });
    });
  });

  describe('executeTests', () => {
    const sampleTests: E2ETestCase[] = [
      {
        id: 'test-1',
        name: 'Sample Test 1',
        description: 'Test description',
        priority: 'high',
        tags: ['component', 'automated'],
        steps: [
          {
            id: 'step-1',
            action: 'navigate',
            description: 'Navigate to page',
            value: '/test-page'
          },
          {
            id: 'step-2',
            action: 'click',
            selector: '[data-testid="button"]',
            description: 'Click button'
          }
        ],
        expectedOutcome: 'Test passes',
        preconditions: ['App is running'],
        testData: {},
        dependencies: []
      }
    ];

    it('should execute tests successfully', async () => {
      const result = await playwrightIntegration.executeTests(sampleTests);

      expect(result).toMatchObject({
        executionId: expect.any(String),
        testResults: expect.any(Array),
        summary: expect.objectContaining({
          total: 1,
          passed: expect.any(Number),
          failed: expect.any(Number),
          duration: expect.any(Number),
          successRate: expect.any(Number)
        }),
        failures: expect.any(Array),
        performance: expect.any(Object),
        artifacts: expect.any(Array)
      });

      expect(result.testResults.length).toBe(1);
    });

    it('should provide performance metrics', async () => {
      const result = await playwrightIntegration.executeTests(sampleTests);

      expect(result.performance).toMatchObject({
        avgTestDuration: expect.any(Number),
        slowestTests: expect.any(Array),
        browserPerformance: expect.any(Object),
        memoryUsage: expect.any(Number),
        parallelEfficiency: expect.any(Number)
      });
    });

    it('should handle test failures gracefully', async () => {
      // Mock a scenario where tests might fail randomly
      const result = await playwrightIntegration.executeTests(sampleTests);

      // Check that failures are properly recorded
      expect(result.summary.total).toBe(result.summary.passed + result.summary.failed + result.summary.skipped + result.summary.flaky);
    });
  });

  describe('analyzeTestCoverage', () => {
    const sampleTests: E2ETestCase[] = [
      {
        id: 'test-coverage',
        name: 'Coverage Test',
        description: 'Test for coverage analysis',
        priority: 'medium',
        tags: ['component'],
        steps: [
          {
            id: 'step-1',
            action: 'click',
            selector: '[data-component="comp1"]',
            description: 'Test component 1'
          }
        ],
        expectedOutcome: 'Component tested',
        preconditions: [],
        testData: {},
        dependencies: ['comp1']
      }
    ];

    it('should analyze test coverage correctly', async () => {
      const coverage = await playwrightIntegration.analyzeTestCoverage(sampleTests, mockDependencyAnalysis);

      expect(coverage).toMatchObject({
        componentCoverage: expect.any(Number),
        userFlowCoverage: expect.any(Number),
        criticalPathCoverage: expect.any(Number),
        edgeCaseCoverage: expect.any(Number),
        riskCoverage: expect.objectContaining({
          high: expect.any(Number),
          medium: expect.any(Number),
          low: expect.any(Number)
        })
      });

      expect(coverage.componentCoverage).toBeGreaterThanOrEqual(0);
      expect(coverage.componentCoverage).toBeLessThanOrEqual(1);
    });
  });

  describe('generateTestRecommendations', () => {
    const sampleTests: E2ETestCase[] = [
      {
        id: 'test-rec',
        name: 'Test for recommendations',
        description: 'Test description',
        priority: 'low',
        tags: ['component'],
        steps: Array(25).fill(0).map((_, i) => ({
          id: `step-${i}`,
          action: 'click' as const,
          description: `Step ${i}`
        })), // Complex test with many steps
        expectedOutcome: 'Test passes',
        preconditions: [],
        testData: {},
        dependencies: []
      }
    ];

    const sampleExecutionPlan = {
      phases: [
        {
          id: 'phase-1',
          name: 'Test Phase',
          tests: ['test-rec'],
          dependencies: [],
          estimatedDuration: 2000000, // 33+ minutes to trigger performance recommendation
          canRunInParallel: true
        }
      ],
      totalEstimatedTime: 2000000,
      parallelization: {
        maxParallel: 2,
        grouping: 'by_priority' as const
      },
      retryStrategy: {
        maxRetries: 2,
        retryOnFailure: true,
        flakyTestHandling: 'retry' as const
      }
    };

    it('should generate coverage recommendations for small test suites', () => {
      const recommendations = playwrightIntegration.generateTestRecommendations(
        [], // Empty test array
        mockDependencyAnalysis,
        sampleExecutionPlan
      );

      const coverageRec = recommendations.find(r => r.type === 'coverage');
      expect(coverageRec).toBeDefined();
      expect(coverageRec?.title).toBe('Increase Test Coverage');
    });

    it('should generate performance recommendations for long execution times', () => {
      const recommendations = playwrightIntegration.generateTestRecommendations(
        sampleTests,
        mockDependencyAnalysis,
        sampleExecutionPlan
      );

      const performanceRec = recommendations.find(r => r.type === 'performance');
      expect(performanceRec).toBeDefined();
      expect(performanceRec?.title).toBe('Optimize Test Execution Time');
    });

    it('should generate maintenance recommendations for complex tests', () => {
      const recommendations = playwrightIntegration.generateTestRecommendations(
        sampleTests,
        mockDependencyAnalysis,
        sampleExecutionPlan
      );

      const maintenanceRec = recommendations.find(r => r.type === 'maintenance');
      expect(maintenanceRec).toBeDefined();
      expect(maintenanceRec?.title).toBe('Simplify Complex Tests');
    });
  });

  describe('event handling', () => {
    it('should emit events during test generation', async () => {
      const eventSpy = vi.spyOn(playwrightIntegration, 'emit');
      
      const testRequest: TestGenerationRequest = {
        id: 'event-test',
        sourceAnalysis: mockDependencyAnalysis,
        targetComponents: [],
        testTypes: ['smoke'],
        userFlows: [],
        coverage: { minCoverage: 0.5, includeEdgeCases: false, includeCriticalPaths: false },
        constraints: { maxTests: 5, maxDuration: 300000, browser: ['chromium'] }
      };

      await playwrightIntegration.generateE2ETests(testRequest);

      expect(eventSpy).toHaveBeenCalledWith('testGenerationStarted', testRequest);
      expect(eventSpy).toHaveBeenCalledWith('testGenerationCompleted', expect.any(Object));
    });

    it('should emit events during test execution', async () => {
      const eventSpy = vi.spyOn(playwrightIntegration, 'emit');
      const sampleTests: E2ETestCase[] = [{
        id: 'event-exec-test',
        name: 'Event Test',
        description: 'Test for events',
        priority: 'medium',
        tags: ['test'],
        steps: [{
          id: 'step-1',
          action: 'navigate',
          description: 'Navigate',
          value: '/'
        }],
        expectedOutcome: 'Success',
        preconditions: [],
        testData: {},
        dependencies: []
      }];

      await playwrightIntegration.executeTests(sampleTests);

      expect(eventSpy).toHaveBeenCalledWith('testExecutionStarted', expect.any(Object));
      expect(eventSpy).toHaveBeenCalledWith('testExecutionCompleted', expect.any(Object));
    });
  });
});