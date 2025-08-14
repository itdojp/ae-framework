/**
 * Test Suite for Intelligent Test Selection System (Phase 3.2)
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { IntelligentTestSelection, type TestSelectionRequest, type CodeChange, type TestInventory } from '../../src/testing/intelligent-test-selection.js';
import type { SequentialInferenceEngine } from '../../src/engines/sequential-inference-engine.js';
import type { DependencyAnalysisResult } from '../../src/analysis/dependency-analyzer.js';

// Mock SequentialInferenceEngine
const mockInferenceEngine: SequentialInferenceEngine = {
  processComplexQuery: vi.fn().mockResolvedValue({
    id: 'test-selection-query',
    status: 'completed',
    result: { 
      selectedTests: ['test-1', 'test-2'],
      reasoning: 'Tests selected based on risk analysis',
      confidence: 0.85
    },
    reasoning: [
      { step: 1, description: 'Analyzed code changes', confidence: 0.9 },
      { step: 2, description: 'Evaluated test coverage', confidence: 0.8 }
    ],
    confidence: 0.85
  }),
  analyzeImpact: vi.fn(),
  evaluateEvidence: vi.fn(),
  reasonStep: vi.fn(),
  synthesizeResults: vi.fn(),
  on: vi.fn(),
  emit: vi.fn()
} as any;

const mockDependencyAnalysis: DependencyAnalysisResult = {
  id: 'test-selection-analysis',
  timestamp: new Date(),
  graph: {
    nodes: [
      { id: 'service-a', name: 'ServiceA', type: 'service', dependencies: [], metadata: { importance: 'critical', complexity: 4 } },
      { id: 'service-b', name: 'ServiceB', type: 'service', dependencies: ['service-a'], metadata: { importance: 'high', complexity: 3 } },
      { id: 'util-c', name: 'UtilC', type: 'utility', dependencies: [], metadata: { importance: 'medium', complexity: 1 } }
    ],
    edges: [
      { from: 'service-b', to: 'service-a', type: 'dependency', weight: 1 }
    ]
  },
  nodes: [
    { id: 'service-a', name: 'ServiceA', type: 'service', dependencies: [], metadata: { importance: 'critical', complexity: 4 } },
    { id: 'service-b', name: 'ServiceB', type: 'service', dependencies: ['service-a'], metadata: { importance: 'high', complexity: 3 } },
    { id: 'util-c', name: 'UtilC', type: 'utility', dependencies: [], metadata: { importance: 'medium', complexity: 1 } }
  ],
  circularDependencies: [],
  criticalPaths: [
    { id: 'critical-path-1', nodes: ['service-a', 'service-b'], weight: 2, description: 'Main service path' }
  ],
  riskAssessment: {
    overallRisk: 'medium',
    riskFactors: [
      {
        id: 'rf-1',
        type: 'complexity',
        severity: 'high',
        affectedNodes: ['service-a'],
        description: 'High complexity service',
        mitigation: 'Increase test coverage'
      }
    ],
    recommendations: []
  },
  optimizations: []
};

describe('IntelligentTestSelection', () => {
  let testSelection: IntelligentTestSelection;

  beforeEach(() => {
    testSelection = new IntelligentTestSelection(mockInferenceEngine);
  });

  describe('constructor', () => {
    it('should initialize with inference engine', () => {
      expect(testSelection).toBeInstanceOf(IntelligentTestSelection);
    });

    it('should accept custom config', () => {
      const customConfig = {
        riskThreshold: 0.8,
        maxTestsPerComponent: 10,
        enableMLPrediction: false
      };
      const selection = new IntelligentTestSelection(mockInferenceEngine, customConfig);
      expect(selection).toBeInstanceOf(IntelligentTestSelection);
    });
  });

  describe('selectTests', () => {
    const sampleCodeChanges: CodeChange[] = [
      {
        id: 'change-1',
        type: 'modification',
        filePath: 'src/services/service-a.ts',
        componentId: 'service-a',
        impact: 'high',
        changeType: 'logic',
        linesChanged: 25,
        additions: 15,
        deletions: 10,
        riskScore: 0.8,
        description: 'Updated authentication logic'
      },
      {
        id: 'change-2',
        type: 'addition',
        filePath: 'src/utils/util-c.ts',
        componentId: 'util-c',
        impact: 'medium',
        changeType: 'feature',
        linesChanged: 12,
        additions: 12,
        deletions: 0,
        riskScore: 0.4,
        description: 'Added new utility function'
      }
    ];

    const sampleTestInventory: TestInventory = {
      id: 'inventory-1',
      timestamp: new Date(),
      totalTests: 150,
      testSuites: [
        {
          id: 'unit-tests',
          name: 'Unit Tests',
          type: 'unit',
          tests: [
            {
              id: 'test-service-a-1',
              name: 'ServiceA Authentication Test',
              type: 'unit',
              filePath: 'tests/unit/service-a.test.ts',
              componentCoverage: ['service-a'],
              priority: 'critical',
              executionTime: 250,
              lastRun: new Date('2025-08-10'),
              successRate: 0.95,
              tags: ['auth', 'service']
            },
            {
              id: 'test-util-c-1',
              name: 'UtilC Helper Functions Test',
              type: 'unit',
              filePath: 'tests/unit/util-c.test.ts',
              componentCoverage: ['util-c'],
              priority: 'medium',
              executionTime: 150,
              lastRun: new Date('2025-08-12'),
              successRate: 0.98,
              tags: ['utility']
            }
          ]
        },
        {
          id: 'integration-tests',
          name: 'Integration Tests',
          type: 'integration',
          tests: [
            {
              id: 'test-integration-1',
              name: 'Service Integration Test',
              type: 'integration',
              filePath: 'tests/integration/services.test.ts',
              componentCoverage: ['service-a', 'service-b'],
              priority: 'high',
              executionTime: 2000,
              lastRun: new Date('2025-08-11'),
              successRate: 0.92,
              tags: ['integration', 'services']
            }
          ]
        }
      ],
      coverage: {
        overall: 0.85,
        byComponent: {
          'service-a': 0.90,
          'service-b': 0.80,
          'util-c': 0.75
        },
        byTestType: {
          unit: 0.88,
          integration: 0.82,
          e2e: 0.70
        }
      },
      metrics: {
        avgExecutionTime: 800,
        flakyTests: 3,
        recentFailures: 5
      }
    };

    const testSelectionRequest: TestSelectionRequest = {
      id: 'selection-req-1',
      changes: sampleCodeChanges,
      testInventory: sampleTestInventory,
      dependencyAnalysis: mockDependencyAnalysis,
      constraints: {
        maxExecutionTime: 600000, // 10 minutes
        maxTests: 50,
        minCoverage: 0.80,
        budgetLimits: {
          timePerTest: 5000,
          totalBudget: 300000
        }
      },
      strategy: 'risk_based',
      preferences: {
        prioritizeRecentChanges: true,
        includeFlakyTests: false,
        parallelExecution: true,
        regressionFocus: true
      }
    };

    it('should select tests based on code changes and risk analysis', async () => {
      const result = await testSelection.selectTests(testSelectionRequest);

      expect(result).toMatchObject({
        requestId: 'selection-req-1',
        selectedTests: expect.objectContaining({
          id: expect.any(String),
          name: expect.any(String),
          tests: expect.any(Array),
          totalTests: expect.any(Number),
          estimatedExecutionTime: expect.any(Number),
          coverageProjection: expect.any(Number)
        }),
        reasoning: expect.objectContaining({
          strategy: expect.any(String),
          factors: expect.any(Array),
          tradeoffs: expect.any(Array),
          confidence: expect.any(Number)
        }),
        optimization: expect.any(Object),
        recommendations: expect.any(Array)
      });

      expect(result.selectedTests.tests.length).toBeGreaterThan(0);
      expect(result.selectedTests.tests.length).toBeLessThanOrEqual(testSelectionRequest.constraints.maxTests);
    });

    it('should respect execution time constraints', async () => {
      const result = await testSelection.selectTests(testSelectionRequest);

      expect(result.selectedTests.estimatedExecutionTime).toBeLessThanOrEqual(
        testSelectionRequest.constraints.maxExecutionTime
      );
    });

    it('should prioritize tests covering changed components', async () => {
      const result = await testSelection.selectTests(testSelectionRequest);

      const changedComponents = sampleCodeChanges.map(c => c.componentId);
      const selectedTests = result.selectedTests.tests;
      
      const testsForChangedComponents = selectedTests.filter(test =>
        test.componentCoverage.some(comp => changedComponents.includes(comp))
      );

      expect(testsForChangedComponents.length).toBeGreaterThan(0);
    });

    it('should apply risk-based selection strategy', async () => {
      const riskBasedRequest = {
        ...testSelectionRequest,
        strategy: 'risk_based' as const
      };

      const result = await testSelection.selectTests(riskBasedRequest);

      expect(result.reasoning.strategy).toBe('risk_based');
      
      // High-risk changes should result in more selected tests
      const highRiskChanges = sampleCodeChanges.filter(c => c.riskScore > 0.7);
      if (highRiskChanges.length > 0) {
        expect(result.selectedTests.tests.length).toBeGreaterThan(1);
      }
    });

    it('should provide meaningful selection reasoning', async () => {
      const result = await testSelection.selectTests(testSelectionRequest);

      expect(result.reasoning.factors.length).toBeGreaterThan(0);
      expect(result.reasoning.confidence).toBeGreaterThan(0);
      expect(result.reasoning.confidence).toBeLessThanOrEqual(1);
      
      result.reasoning.factors.forEach(factor => {
        expect(factor).toMatchObject({
          name: expect.any(String),
          weight: expect.any(Number),
          description: expect.any(String),
          impact: expect.stringMatching(/high|medium|low/)
        });
      });
    });
  });

  describe('analyzeCoverage', () => {
    const sampleChanges: CodeChange[] = [
      {
        id: 'coverage-change-1',
        type: 'modification',
        filePath: 'src/services/service-a.ts',
        componentId: 'service-a',
        impact: 'high',
        changeType: 'logic',
        linesChanged: 20,
        additions: 12,
        deletions: 8,
        riskScore: 0.7,
        description: 'Service modification'
      }
    ];

    const sampleTestInventory: TestInventory = {
      id: 'coverage-inventory',
      timestamp: new Date(),
      totalTests: 100,
      testSuites: [
        {
          id: 'suite-1',
          name: 'Test Suite 1',
          type: 'unit',
          tests: [
            {
              id: 'coverage-test-1',
              name: 'Coverage Test 1',
              type: 'unit',
              filePath: 'tests/unit/test1.ts',
              componentCoverage: ['service-a'],
              priority: 'high',
              executionTime: 200,
              lastRun: new Date(),
              successRate: 0.95,
              tags: ['coverage']
            }
          ]
        }
      ],
      coverage: {
        overall: 0.80,
        byComponent: {
          'service-a': 0.85
        },
        byTestType: {
          unit: 0.80
        }
      },
      metrics: {
        avgExecutionTime: 500,
        flakyTests: 1,
        recentFailures: 2
      }
    };

    it('should analyze coverage comprehensively', async () => {
      const result = await testSelection.analyzeCoverage(sampleChanges, sampleTestInventory);

      expect(result).toMatchObject({
        overallCoverage: expect.any(Number),
        componentCoverage: expect.any(Object),
        riskCoverage: expect.any(Object),
        gaps: expect.any(Array),
        recommendations: expect.any(Array),
        projectedCoverage: expect.any(Object)
      });

      expect(result.overallCoverage).toBeGreaterThanOrEqual(0);
      expect(result.overallCoverage).toBeLessThanOrEqual(1);
    });

    it('should identify coverage gaps', async () => {
      const result = await testSelection.analyzeCoverage(sampleChanges, sampleTestInventory);

      expect(result.gaps).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            type: expect.stringMatching(/component|path|scenario/),
            severity: expect.stringMatching(/high|medium|low/),
            description: expect.any(String),
            impact: expect.any(String)
          })
        ])
      );
    });

    it('should provide coverage recommendations', async () => {
      const result = await testSelection.analyzeCoverage(sampleChanges, sampleTestInventory);

      expect(result.recommendations.length).toBeGreaterThan(0);
      result.recommendations.forEach(rec => {
        expect(rec).toMatchObject({
          type: expect.any(String),
          priority: expect.stringMatching(/high|medium|low/),
          description: expect.any(String),
          effort: expect.stringMatching(/high|medium|low/),
          impact: expect.any(String)
        });
      });
    });
  });

  describe('predictExecutionTime', () => {
    const sampleSelectedTestSuite = {
      id: 'prediction-suite',
      name: 'Prediction Test Suite',
      tests: [
        {
          id: 'pred-test-1',
          name: 'Prediction Test 1',
          type: 'unit' as const,
          filePath: 'tests/pred1.ts',
          componentCoverage: ['service-a'],
          priority: 'high' as const,
          executionTime: 1000,
          lastRun: new Date(),
          successRate: 0.95,
          tags: ['prediction']
        },
        {
          id: 'pred-test-2',
          name: 'Prediction Test 2',
          type: 'integration' as const,
          filePath: 'tests/pred2.ts',
          componentCoverage: ['service-b'],
          priority: 'medium' as const,
          executionTime: 3000,
          lastRun: new Date(),
          successRate: 0.88,
          tags: ['prediction']
        }
      ],
      totalTests: 2,
      estimatedExecutionTime: 4000,
      coverageProjection: 0.75
    };

    it('should predict execution time accurately', () => {
      const prediction = testSelection.predictExecutionTime(sampleSelectedTestSuite);

      expect(prediction).toMatchObject({
        estimatedTime: expect.any(Number),
        confidence: expect.any(Number),
        breakdown: expect.objectContaining({
          sequential: expect.any(Number),
          parallel: expect.any(Number),
          overhead: expect.any(Number)
        }),
        factors: expect.any(Array),
        optimization: expect.any(Object)
      });

      expect(prediction.estimatedTime).toBeGreaterThan(0);
      expect(prediction.confidence).toBeGreaterThan(0);
      expect(prediction.confidence).toBeLessThanOrEqual(1);
    });

    it('should consider parallelization in predictions', () => {
      const prediction = testSelection.predictExecutionTime(sampleSelectedTestSuite);

      expect(prediction.breakdown.parallel).toBeLessThan(prediction.breakdown.sequential);
      expect(prediction.breakdown.overhead).toBeGreaterThan(0);
    });

    it('should provide optimization suggestions', () => {
      const prediction = testSelection.predictExecutionTime(sampleSelectedTestSuite);

      expect(prediction.optimization).toMatchObject({
        parallelizationGains: expect.any(Number),
        recommendations: expect.any(Array),
        potentialSavings: expect.any(Number)
      });

      expect(prediction.optimization.recommendations.length).toBeGreaterThan(0);
    });
  });

  describe('event handling', () => {
    it('should emit events during test selection', async () => {
      const eventSpy = vi.spyOn(testSelection, 'emit');
      
      const testRequest: TestSelectionRequest = {
        id: 'event-test',
        changes: [],
        testInventory: {
          id: 'empty-inventory',
          timestamp: new Date(),
          totalTests: 0,
          testSuites: [],
          coverage: { overall: 0, byComponent: {}, byTestType: {} },
          metrics: { avgExecutionTime: 0, flakyTests: 0, recentFailures: 0 }
        },
        dependencyAnalysis: mockDependencyAnalysis,
        constraints: {
          maxExecutionTime: 300000,
          maxTests: 10,
          minCoverage: 0.5,
          budgetLimits: { timePerTest: 1000, totalBudget: 100000 }
        },
        strategy: 'balanced',
        preferences: {
          prioritizeRecentChanges: false,
          includeFlakyTests: false,
          parallelExecution: false,
          regressionFocus: false
        }
      };

      await testSelection.selectTests(testRequest);

      expect(eventSpy).toHaveBeenCalledWith('testSelectionStarted', testRequest);
      expect(eventSpy).toHaveBeenCalledWith('testSelectionCompleted', expect.any(Object));
    });

    it('should emit progress events during analysis', async () => {
      const eventSpy = vi.spyOn(testSelection, 'emit');
      
      const sampleChanges: CodeChange[] = [
        {
          id: 'progress-change',
          type: 'modification',
          filePath: 'src/test-file.ts',
          componentId: 'test-component',
          impact: 'medium',
          changeType: 'logic',
          linesChanged: 10,
          additions: 6,
          deletions: 4,
          riskScore: 0.5,
          description: 'Progress test change'
        }
      ];

      const testInventory: TestInventory = {
        id: 'progress-inventory',
        timestamp: new Date(),
        totalTests: 5,
        testSuites: [{
          id: 'progress-suite',
          name: 'Progress Suite',
          type: 'unit',
          tests: []
        }],
        coverage: { overall: 0.5, byComponent: {}, byTestType: {} },
        metrics: { avgExecutionTime: 1000, flakyTests: 0, recentFailures: 0 }
      };

      await testSelection.analyzeCoverage(sampleChanges, testInventory);

      expect(eventSpy).toHaveBeenCalledWith('coverageAnalysisStarted', expect.any(Object));
      expect(eventSpy).toHaveBeenCalledWith('coverageAnalysisCompleted', expect.any(Object));
    });
  });

  describe('integration with inference engine', () => {
    it('should utilize inference engine for complex decisions', async () => {
      const testRequest: TestSelectionRequest = {
        id: 'inference-test',
        changes: [
          {
            id: 'complex-change',
            type: 'modification',
            filePath: 'src/complex-service.ts',
            componentId: 'complex-service',
            impact: 'high',
            changeType: 'logic',
            linesChanged: 50,
            additions: 30,
            deletions: 20,
            riskScore: 0.9,
            description: 'Complex service modification'
          }
        ],
        testInventory: {
          id: 'complex-inventory',
          timestamp: new Date(),
          totalTests: 100,
          testSuites: [],
          coverage: { overall: 0.8, byComponent: {}, byTestType: {} },
          metrics: { avgExecutionTime: 2000, flakyTests: 5, recentFailures: 8 }
        },
        dependencyAnalysis: mockDependencyAnalysis,
        constraints: {
          maxExecutionTime: 1200000,
          maxTests: 30,
          minCoverage: 0.85,
          budgetLimits: { timePerTest: 10000, totalBudget: 300000 }
        },
        strategy: 'ml_optimized',
        preferences: {
          prioritizeRecentChanges: true,
          includeFlakyTests: false,
          parallelExecution: true,
          regressionFocus: true
        }
      };

      await testSelection.selectTests(testRequest);

      expect(mockInferenceEngine.processComplexQuery).toHaveBeenCalledWith(
        expect.objectContaining({
          description: expect.stringContaining('test selection'),
          context: expect.objectContaining({
            changes: testRequest.changes,
            constraints: testRequest.constraints,
            strategy: testRequest.strategy
          })
        })
      );
    });
  });
});