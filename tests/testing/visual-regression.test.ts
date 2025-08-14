/**
 * Test Suite for Visual Regression Testing System (Phase 3.2)
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { VisualRegressionTesting, type VisualTestRequest, type VisualTestSuite, type PlaywrightConfig } from '../../src/testing/visual-regression.js';
import type { DependencyAnalysisResult } from '../../src/analysis/dependency-analyzer.js';

const mockDependencyAnalysis: DependencyAnalysisResult = {
  id: 'visual-analysis',
  timestamp: new Date(),
  graph: {
    nodes: [
      { id: 'ui-comp1', name: 'HeaderComponent', type: 'ui-component', dependencies: [], metadata: { importance: 'critical', complexity: 3 } },
      { id: 'ui-comp2', name: 'NavComponent', type: 'ui-component', dependencies: ['ui-comp1'], metadata: { importance: 'high', complexity: 2 } }
    ],
    edges: [{ from: 'ui-comp2', to: 'ui-comp1', type: 'dependency', weight: 1 }]
  },
  nodes: [
    { id: 'ui-comp1', name: 'HeaderComponent', type: 'ui-component', dependencies: [], metadata: { importance: 'critical', complexity: 3 } },
    { id: 'ui-comp2', name: 'NavComponent', type: 'ui-component', dependencies: ['ui-comp1'], metadata: { importance: 'high', complexity: 2 } }
  ],
  circularDependencies: [],
  criticalPaths: [],
  riskAssessment: {
    overallRisk: 'low',
    riskFactors: [],
    recommendations: []
  },
  optimizations: []
};

const mockPlaywrightConfig: PlaywrightConfig = {
  baseURL: 'http://localhost:3000',
  browserType: 'chromium',
  headless: true,
  viewport: { width: 1280, height: 720 },
  timeout: 30000,
  retries: 2,
  outputDir: './test-results',
  screenshotMode: 'only-on-failure',
  videoMode: 'retain-on-failure'
};

describe('VisualRegressionTesting', () => {
  let visualTesting: VisualRegressionTesting;

  beforeEach(() => {
    visualTesting = new VisualRegressionTesting();
  });

  describe('constructor', () => {
    it('should initialize with default config', () => {
      expect(visualTesting).toBeInstanceOf(VisualRegressionTesting);
    });

    it('should accept custom config overrides', () => {
      const customConfig = {
        threshold: 0.05,
        includeText: false,
        browsers: ['firefox', 'webkit']
      };
      const visual = new VisualRegressionTesting(customConfig);
      expect(visual).toBeInstanceOf(VisualRegressionTesting);
    });
  });

  describe('generateVisualTests', () => {
    const visualRequest: VisualTestRequest = {
      id: 'visual-req-1',
      sourceAnalysis: mockDependencyAnalysis,
      testTargets: [
        {
          type: 'component',
          identifier: 'header-component',
          url: '/components/header',
          selector: '[data-testid="header"]'
        },
        {
          type: 'page',
          identifier: 'homepage',
          url: '/',
          selector: undefined
        }
      ],
      config: {
        threshold: 0.03,
        browsers: ['chromium']
      },
      baselineMode: 'compare',
      scope: {
        includeComponents: true,
        includePages: true,
        includeCriticalPaths: false
      }
    };

    it('should generate comprehensive visual test suite', async () => {
      const result = await visualTesting.generateVisualTests(visualRequest);

      expect(result).toMatchObject({
        id: 'visual-req-1',
        name: expect.stringContaining('Visual Test Suite'),
        description: expect.any(String),
        tests: expect.any(Array),
        config: expect.any(Object),
        baseline: expect.objectContaining({
          version: expect.any(String),
          timestamp: expect.any(Date)
        })
      });

      expect(result.tests.length).toBeGreaterThan(0);
    });

    it('should generate component tests when includeComponents is true', async () => {
      const result = await visualTesting.generateVisualTests(visualRequest);
      
      const componentTests = result.tests.filter(test => 
        test.tags.includes('component')
      );
      expect(componentTests.length).toBeGreaterThan(0);
    });

    it('should generate page tests when includePages is true', async () => {
      const result = await visualTesting.generateVisualTests(visualRequest);
      
      const pageTests = result.tests.filter(test => 
        test.tags.includes('page')
      );
      expect(pageTests.length).toBeGreaterThan(0);
    });

    it('should respect config overrides', async () => {
      const result = await visualTesting.generateVisualTests(visualRequest);
      
      expect(result.config.threshold).toBe(0.03);
      expect(result.config.browsers).toContain('chromium');
    });

    it('should set appropriate test priorities', async () => {
      const result = await visualTesting.generateVisualTests(visualRequest);
      
      const criticalTests = result.tests.filter(test => test.priority === 'critical');
      const highTests = result.tests.filter(test => test.priority === 'high');
      
      expect(criticalTests.length + highTests.length).toBeGreaterThan(0);
    });
  });

  describe('executeVisualTests', () => {
    let sampleTestSuite: VisualTestSuite;

    beforeEach(async () => {
      const visualRequest: VisualTestRequest = {
        id: 'exec-test',
        sourceAnalysis: mockDependencyAnalysis,
        testTargets: [
          {
            type: 'component',
            identifier: 'test-comp',
            url: '/test',
            selector: '[data-testid="test"]'
          }
        ],
        config: { threshold: 0.02 },
        baselineMode: 'compare',
        scope: {
          includeComponents: true,
          includePages: false,
          includeCriticalPaths: false
        }
      };
      sampleTestSuite = await visualTesting.generateVisualTests(visualRequest);
    });

    it('should execute visual tests successfully', async () => {
      const result = await visualTesting.executeVisualTests(sampleTestSuite, mockPlaywrightConfig);

      expect(result).toMatchObject({
        suiteId: sampleTestSuite.id,
        executionId: expect.any(String),
        timestamp: expect.any(Date),
        summary: expect.objectContaining({
          total: expect.any(Number),
          passed: expect.any(Number),
          failed: expect.any(Number),
          newBaselines: expect.any(Number),
          updatedBaselines: expect.any(Number)
        }),
        results: expect.any(Array),
        analysis: expect.any(Object),
        recommendations: expect.any(Array)
      });

      expect(result.results.length).toBeGreaterThan(0);
    });

    it('should provide visual analysis', async () => {
      const result = await visualTesting.executeVisualTests(sampleTestSuite, mockPlaywrightConfig);

      expect(result.analysis).toMatchObject({
        changePatterns: expect.any(Array),
        impactAssessment: expect.objectContaining({
          overallImpact: expect.stringMatching(/minimal|moderate|significant|major/),
          userExperienceImpact: expect.any(Number),
          affectedUserFlows: expect.any(Array),
          businessImpact: expect.any(String),
          technicalImpact: expect.any(String)
        }),
        riskFactors: expect.any(Array),
        trends: expect.any(Array)
      });
    });

    it('should generate meaningful recommendations', async () => {
      const result = await visualTesting.executeVisualTests(sampleTestSuite, mockPlaywrightConfig);

      expect(result.recommendations).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            id: expect.any(String),
            type: expect.stringMatching(/threshold|coverage|maintenance|optimization/),
            priority: expect.stringMatching(/high|medium|low/),
            title: expect.any(String),
            description: expect.any(String),
            impact: expect.any(String),
            effort: expect.stringMatching(/low|medium|high/),
            implementation: expect.any(Array)
          })
        ])
      );
    });

    it('should test across multiple viewports and browsers', async () => {
      const result = await visualTesting.executeVisualTests(sampleTestSuite, mockPlaywrightConfig);

      const viewportResults = new Set(result.results.map(r => `${r.viewport.width}x${r.viewport.height}`));
      const browserResults = new Set(result.results.map(r => r.browser));

      expect(viewportResults.size).toBeGreaterThan(1); // Multiple viewports
      expect(browserResults.size).toBeGreaterThan(0); // At least one browser
    });
  });

  describe('manageBaselines', () => {
    let sampleTestSuite: VisualTestSuite;

    beforeEach(async () => {
      const visualRequest: VisualTestRequest = {
        id: 'baseline-test',
        sourceAnalysis: mockDependencyAnalysis,
        testTargets: [
          {
            type: 'component',
            identifier: 'baseline-comp',
            url: '/baseline',
            selector: '[data-testid="baseline"]'
          }
        ],
        config: {},
        baselineMode: 'create',
        scope: {
          includeComponents: true,
          includePages: false,
          includeCriticalPaths: false
        }
      };
      sampleTestSuite = await visualTesting.generateVisualTests(visualRequest);
    });

    it('should create new baselines', async () => {
      const result = await visualTesting.manageBaselines(sampleTestSuite, 'create');

      expect(result).toMatchObject({
        created: expect.any(Number),
        updated: expect.any(Number),
        skipped: expect.any(Number)
      });

      expect(result.created).toBeGreaterThan(0);
    });

    it('should update existing baselines', async () => {
      // First create baselines
      await visualTesting.manageBaselines(sampleTestSuite, 'create');
      
      // Then update them
      const result = await visualTesting.manageBaselines(sampleTestSuite, 'update');

      expect(result).toMatchObject({
        created: expect.any(Number),
        updated: expect.any(Number),
        skipped: expect.any(Number)
      });
    });

    it('should handle selective baseline updates', async () => {
      const result = await visualTesting.manageBaselines(sampleTestSuite, 'selective');

      expect(result).toMatchObject({
        created: expect.any(Number),
        updated: expect.any(Number),
        skipped: expect.any(Number)
      });

      // In selective mode, some tests should be skipped
      expect(result.created + result.updated + result.skipped).toBe(sampleTestSuite.tests.length);
    });
  });

  describe('analyzeVisualChanges', () => {
    const sampleResults = [
      {
        testId: 'test-1',
        status: 'passed' as const,
        comparison: {
          pixelDifference: 100,
          percentageDifference: 0.01,
          threshold: 0.02,
          passed: true,
          regions: []
        },
        browser: 'chromium',
        viewport: { name: 'desktop', width: 1280, height: 720 },
        artifacts: [],
        executionTime: 1500
      },
      {
        testId: 'test-2',
        status: 'failed' as const,
        comparison: {
          pixelDifference: 500,
          percentageDifference: 0.05,
          threshold: 0.02,
          passed: false,
          regions: [
            {
              x: 100, y: 100, width: 200, height: 150,
              severity: 'medium' as const,
              description: 'Layout shift detected'
            }
          ]
        },
        browser: 'chromium',
        viewport: { name: 'desktop', width: 1280, height: 720 },
        artifacts: [],
        executionTime: 2000
      }
    ];

    it('should analyze visual changes and assess impact', () => {
      const impact = visualTesting.analyzeVisualChanges(sampleResults, mockDependencyAnalysis);

      expect(impact).toMatchObject({
        overallImpact: expect.stringMatching(/minimal|moderate|significant|major/),
        userExperienceImpact: expect.any(Number),
        affectedUserFlows: expect.any(Array),
        businessImpact: expect.any(String),
        technicalImpact: expect.any(String)
      });

      expect(impact.userExperienceImpact).toBeGreaterThanOrEqual(0);
      expect(impact.userExperienceImpact).toBeLessThanOrEqual(1);
    });

    it('should classify impact levels correctly', () => {
      // Test with all failing results for major impact
      const allFailedResults = sampleResults.map(r => ({ ...r, status: 'failed' as const }));
      const majorImpact = visualTesting.analyzeVisualChanges(allFailedResults, mockDependencyAnalysis);
      
      expect(['significant', 'major']).toContain(majorImpact.overallImpact);

      // Test with all passing results for minimal impact
      const allPassedResults = sampleResults.map(r => ({ ...r, status: 'passed' as const }));
      const minimalImpact = visualTesting.analyzeVisualChanges(allPassedResults, mockDependencyAnalysis);
      
      expect(minimalImpact.overallImpact).toBe('minimal');
    });

    it('should identify affected user flows', () => {
      const impact = visualTesting.analyzeVisualChanges(sampleResults, mockDependencyAnalysis);
      
      expect(impact.affectedUserFlows).toEqual(
        expect.arrayContaining([
          expect.stringMatching(/flow-.+/)
        ])
      );
    });
  });

  describe('event handling', () => {
    it('should emit events during visual test generation', async () => {
      const eventSpy = vi.spyOn(visualTesting, 'emit');
      
      const visualRequest: VisualTestRequest = {
        id: 'event-test',
        sourceAnalysis: mockDependencyAnalysis,
        testTargets: [],
        config: {},
        baselineMode: 'compare',
        scope: {
          includeComponents: false,
          includePages: false,
          includeCriticalPaths: false
        }
      };

      await visualTesting.generateVisualTests(visualRequest);

      expect(eventSpy).toHaveBeenCalledWith('visualTestGenerationStarted', visualRequest);
      expect(eventSpy).toHaveBeenCalledWith('visualTestGenerationCompleted', expect.any(Object));
    });

    it('should emit events during test execution', async () => {
      const eventSpy = vi.spyOn(visualTesting, 'emit');
      
      const visualRequest: VisualTestRequest = {
        id: 'exec-event-test',
        sourceAnalysis: mockDependencyAnalysis,
        testTargets: [
          {
            type: 'component',
            identifier: 'event-comp',
            url: '/event',
            selector: '[data-testid="event"]'
          }
        ],
        config: {},
        baselineMode: 'compare',
        scope: {
          includeComponents: true,
          includePages: false,
          includeCriticalPaths: false
        }
      };

      const testSuite = await visualTesting.generateVisualTests(visualRequest);
      await visualTesting.executeVisualTests(testSuite, mockPlaywrightConfig);

      expect(eventSpy).toHaveBeenCalledWith('visualTestExecutionStarted', expect.any(Object));
      expect(eventSpy).toHaveBeenCalledWith('visualTestExecutionCompleted', expect.any(Object));
    });

    it('should emit events during baseline management', async () => {
      const eventSpy = vi.spyOn(visualTesting, 'emit');
      
      const visualRequest: VisualTestRequest = {
        id: 'baseline-event-test',
        sourceAnalysis: mockDependencyAnalysis,
        testTargets: [
          {
            type: 'component',
            identifier: 'baseline-event-comp',
            url: '/baseline-event',
            selector: '[data-testid="baseline-event"]'
          }
        ],
        config: {},
        baselineMode: 'create',
        scope: {
          includeComponents: true,
          includePages: false,
          includeCriticalPaths: false
        }
      };

      const testSuite = await visualTesting.generateVisualTests(visualRequest);
      await visualTesting.manageBaselines(testSuite, 'create');

      expect(eventSpy).toHaveBeenCalledWith('baselineManagementStarted', expect.any(Object));
      expect(eventSpy).toHaveBeenCalledWith('baselineManagementCompleted', expect.any(Object));
    });
  });
});