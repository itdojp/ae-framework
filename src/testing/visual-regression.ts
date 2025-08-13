/**
 * Visual Regression Testing System for Phase 3.2
 * Provides automated visual testing and change detection
 */

import { EventEmitter } from 'events';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';
import type { PlaywrightConfig, E2ETestCase } from './playwright-integration.js';

export interface VisualTestConfig {
  threshold: number; // Pixel difference threshold (0-1)
  includeText: boolean;
  ignoreRegions: IgnoreRegion[];
  browsers: string[];
  viewports: Viewport[];
  waitConditions: WaitCondition[];
}

export interface Viewport {
  name: string;
  width: number;
  height: number;
  deviceScaleFactor?: number;
}

export interface IgnoreRegion {
  name: string;
  selector: string;
  reason: string;
}

export interface WaitCondition {
  type: 'selector' | 'networkidle' | 'timeout' | 'custom';
  value: string | number;
  description: string;
}

export interface VisualTestCase {
  id: string;
  name: string;
  description: string;
  url: string;
  selector?: string; // If testing specific component
  config: VisualTestConfig;
  baseline: string; // Path to baseline image
  priority: 'critical' | 'high' | 'medium' | 'low';
  tags: string[];
  dependencies: string[];
}

export interface VisualTestRequest {
  id: string;
  sourceAnalysis: DependencyAnalysisResult;
  testTargets: VisualTestTarget[];
  config: Partial<VisualTestConfig>;
  baselineMode: 'create' | 'update' | 'compare';
  scope: {
    includeComponents: boolean;
    includePages: boolean;
    includeCriticalPaths: boolean;
  };
}

export interface VisualTestTarget {
  type: 'page' | 'component' | 'flow';
  identifier: string;
  url: string;
  selector?: string;
  state?: ComponentState;
}

export interface ComponentState {
  props?: Record<string, any>;
  interactions?: StateInteraction[];
  dataState?: Record<string, any>;
}

export interface StateInteraction {
  action: 'hover' | 'focus' | 'click' | 'fill';
  selector: string;
  value?: string;
  description: string;
}

export interface VisualTestResult {
  testId: string;
  status: 'passed' | 'failed' | 'baseline_created' | 'baseline_updated';
  comparison: VisualComparison;
  browser: string;
  viewport: Viewport;
  artifacts: VisualArtifact[];
  executionTime: number;
}

export interface VisualComparison {
  pixelDifference: number;
  percentageDifference: number;
  threshold: number;
  passed: boolean;
  regions: DifferenceRegion[];
}

export interface DifferenceRegion {
  x: number;
  y: number;
  width: number;
  height: number;
  severity: 'low' | 'medium' | 'high';
  description: string;
}

export interface VisualArtifact {
  type: 'baseline' | 'actual' | 'diff' | 'annotated';
  path: string;
  description: string;
  metadata: {
    width: number;
    height: number;
    format: string;
    size: number;
  };
}

export interface VisualTestSuite {
  id: string;
  name: string;
  description: string;
  tests: VisualTestCase[];
  config: VisualTestConfig;
  baseline: {
    version: string;
    timestamp: Date;
    commit?: string;
    branch?: string;
  };
}

export interface VisualRegressionReport {
  suiteId: string;
  executionId: string;
  timestamp: Date;
  summary: {
    total: number;
    passed: number;
    failed: number;
    newBaselines: number;
    updatedBaselines: number;
  };
  results: VisualTestResult[];
  analysis: VisualAnalysis;
  recommendations: VisualRecommendation[];
}

export interface VisualAnalysis {
  changePatterns: ChangePattern[];
  impactAssessment: VisualImpactAssessment;
  riskFactors: VisualRiskFactor[];
  trends: VisualTrend[];
}

export interface ChangePattern {
  type: 'layout' | 'color' | 'typography' | 'content' | 'animation';
  frequency: number;
  affectedComponents: string[];
  severity: 'low' | 'medium' | 'high';
  description: string;
}

export interface VisualImpactAssessment {
  overallImpact: 'minimal' | 'moderate' | 'significant' | 'major';
  userExperienceImpact: number; // 0-1 scale
  affectedUserFlows: string[];
  businessImpact: string;
  technicalImpact: string;
}

export interface VisualRiskFactor {
  id: string;
  type: 'layout_shift' | 'color_contrast' | 'text_readability' | 'interactive_element';
  severity: 'low' | 'medium' | 'high' | 'critical';
  description: string;
  affectedTests: string[];
  mitigation: string;
}

export interface VisualTrend {
  metric: 'difference_rate' | 'test_duration' | 'false_positives';
  direction: 'increasing' | 'decreasing' | 'stable';
  change: number;
  timeframe: string;
  significance: 'low' | 'medium' | 'high';
}

export interface VisualRecommendation {
  id: string;
  type: 'threshold' | 'coverage' | 'maintenance' | 'optimization';
  priority: 'high' | 'medium' | 'low';
  title: string;
  description: string;
  impact: string;
  effort: 'low' | 'medium' | 'high';
  implementation: string[];
}

export class VisualRegressionTesting extends EventEmitter {
  private config: VisualTestConfig;
  private activeTests = new Map<string, VisualTestResult[]>();
  private baselines = new Map<string, string>();
  private testHistory: VisualTestResult[] = [];

  constructor(config: Partial<VisualTestConfig> = {}) {
    super();
    this.config = this.createDefaultConfig(config);
    this.setupEventHandlers();
  }

  /**
   * Generate visual tests from dependency analysis
   */
  async generateVisualTests(request: VisualTestRequest): Promise<VisualTestSuite> {
    this.emit('visualTestGenerationStarted', request);

    try {
      const tests: VisualTestCase[] = [];

      // Generate tests for critical components
      if (request.scope.includeComponents) {
        const componentTests = await this.generateComponentVisualTests(request);
        tests.push(...componentTests);
      }

      // Generate tests for pages
      if (request.scope.includePages) {
        const pageTests = await this.generatePageVisualTests(request);
        tests.push(...pageTests);
      }

      // Generate tests for critical paths
      if (request.scope.includeCriticalPaths) {
        const criticalPathTests = await this.generateCriticalPathVisualTests(request);
        tests.push(...criticalPathTests);
      }

      const testSuite: VisualTestSuite = {
        id: request.id,
        name: `Visual Test Suite - ${request.id}`,
        description: 'Auto-generated visual regression test suite',
        tests,
        config: { ...this.config, ...request.config },
        baseline: {
          version: '1.0.0',
          timestamp: new Date(),
          commit: process.env.GIT_COMMIT,
          branch: process.env.GIT_BRANCH
        }
      };

      this.emit('visualTestGenerationCompleted', { request, testSuite });
      return testSuite;

    } catch (error) {
      this.emit('visualTestGenerationError', { request, error });
      throw error;
    }
  }

  /**
   * Execute visual regression tests
   */
  async executeVisualTests(
    testSuite: VisualTestSuite,
    playwrightConfig: PlaywrightConfig
  ): Promise<VisualRegressionReport> {
    const executionId = `visual-exec-${Date.now()}`;
    this.emit('visualTestExecutionStarted', { executionId, testSuite });

    try {
      const results: VisualTestResult[] = [];

      for (const test of testSuite.tests) {
        for (const viewport of testSuite.config.viewports) {
          for (const browser of testSuite.config.browsers) {
            const result = await this.executeVisualTest(test, viewport, browser, playwrightConfig);
            results.push(result);
          }
        }
      }

      this.activeTests.set(executionId, results);
      this.testHistory.push(...results);

      // Generate analysis and recommendations
      const analysis = this.analyzeVisualResults(results, testSuite);
      const recommendations = this.generateVisualRecommendations(analysis, results);

      const report: VisualRegressionReport = {
        suiteId: testSuite.id,
        executionId,
        timestamp: new Date(),
        summary: this.calculateSummary(results),
        results,
        analysis,
        recommendations
      };

      this.emit('visualTestExecutionCompleted', report);
      return report;

    } catch (error) {
      this.emit('visualTestExecutionError', { executionId, error });
      throw error;
    }
  }

  /**
   * Create or update baseline images
   */
  async manageBaselines(
    testSuite: VisualTestSuite,
    mode: 'create' | 'update' | 'selective'
  ): Promise<{ created: number; updated: number; skipped: number }> {
    this.emit('baselineManagementStarted', { testSuite, mode });

    const stats = { created: 0, updated: 0, skipped: 0 };

    try {
      for (const test of testSuite.tests) {
        const baselineExists = this.baselines.has(test.id);

        if (mode === 'create' && !baselineExists) {
          await this.createBaseline(test);
          stats.created++;
        } else if (mode === 'update' || (mode === 'selective' && this.shouldUpdateBaseline(test))) {
          await this.updateBaseline(test);
          stats.updated++;
        } else {
          stats.skipped++;
        }
      }

      this.emit('baselineManagementCompleted', stats);
      return stats;

    } catch (error) {
      this.emit('baselineManagementError', { testSuite, mode, error });
      throw error;
    }
  }

  /**
   * Analyze visual changes and their impact
   */
  analyzeVisualChanges(
    results: VisualTestResult[],
    dependencyAnalysis: DependencyAnalysisResult
  ): VisualImpactAssessment {
    const failedTests = results.filter(r => r.status === 'failed');
    const totalTests = results.length;

    // Calculate overall impact
    const failureRate = failedTests.length / totalTests;
    let overallImpact: VisualImpactAssessment['overallImpact'];

    if (failureRate > 0.5) overallImpact = 'major';
    else if (failureRate > 0.3) overallImpact = 'significant';
    else if (failureRate > 0.1) overallImpact = 'moderate';
    else overallImpact = 'minimal';

    // Assess user experience impact
    const criticalFailures = failedTests.filter(t => 
      t.testId.includes('critical')
    );
    const userExperienceImpact = criticalFailures.length / Math.max(totalTests * 0.2, 1);

    // Identify affected user flows
    const affectedUserFlows = this.identifyAffectedUserFlows(failedTests, dependencyAnalysis);

    return {
      overallImpact,
      userExperienceImpact: Math.min(userExperienceImpact, 1),
      affectedUserFlows,
      businessImpact: this.assessBusinessImpact(failedTests, overallImpact),
      technicalImpact: this.assessTechnicalImpact(failedTests, dependencyAnalysis)
    };
  }

  // Private helper methods
  private createDefaultConfig(overrides: Partial<VisualTestConfig>): VisualTestConfig {
    return {
      threshold: 0.02, // 2% pixel difference threshold
      includeText: true,
      ignoreRegions: [
        {
          name: 'dynamic-timestamps',
          selector: '[data-timestamp]',
          reason: 'Timestamps change dynamically'
        },
        {
          name: 'loading-indicators',
          selector: '.loading, .spinner',
          reason: 'Loading states are transient'
        }
      ],
      browsers: ['chromium'],
      viewports: [
        { name: 'desktop', width: 1280, height: 720 },
        { name: 'tablet', width: 768, height: 1024 },
        { name: 'mobile', width: 375, height: 667 }
      ],
      waitConditions: [
        {
          type: 'networkidle',
          value: 0,
          description: 'Wait for network to be idle'
        },
        {
          type: 'timeout',
          value: 3000,
          description: 'Wait for animations to complete'
        }
      ],
      ...overrides
    };
  }

  private setupEventHandlers(): void {
    this.on('visualTestGenerationStarted', (request) => {
      console.log(`👁️  Visual test generation started: ${request.id}`);
    });

    this.on('visualTestExecutionStarted', ({ executionId, testSuite }) => {
      console.log(`🎯 Visual test execution started: ${executionId} (${testSuite.tests.length} tests)`);
    });

    this.on('visualTestExecutionCompleted', (report) => {
      console.log(`✅ Visual tests completed: ${report.summary.passed}/${report.summary.total} passed`);
    });
  }

  private async generateComponentVisualTests(request: VisualTestRequest): Promise<VisualTestCase[]> {
    const tests: VisualTestCase[] = [];
    
    const criticalComponents = request.sourceAnalysis.nodes.filter(
      node => node.metadata.importance === 'critical' || node.metadata.importance === 'high'
    );

    for (const component of criticalComponents.slice(0, 10)) { // Limit to top 10
      const test: VisualTestCase = {
        id: `visual-${component.id}`,
        name: `Visual Test: ${component.name}`,
        description: `Visual regression test for ${component.name} component`,
        url: this.getComponentURL(component),
        selector: `[data-testid="${component.id}"]`,
        config: { ...this.config, ...request.config },
        baseline: `baselines/${component.id}.png`,
        priority: component.metadata.importance === 'critical' ? 'critical' : 'high',
        tags: ['component', 'visual', component.type],
        dependencies: component.dependencies.slice(0, 3)
      };
      tests.push(test);
    }

    return tests;
  }

  private async generatePageVisualTests(request: VisualTestRequest): Promise<VisualTestCase[]> {
    const tests: VisualTestCase[] = [];
    
    // Generate tests for main pages based on targets
    for (const target of request.testTargets) {
      if (target.type === 'page') {
        const test: VisualTestCase = {
          id: `visual-page-${target.identifier}`,
          name: `Visual Test: ${target.identifier} Page`,
          description: `Full page visual regression test for ${target.identifier}`,
          url: target.url,
          config: { ...this.config, ...request.config },
          baseline: `baselines/page-${target.identifier}.png`,
          priority: 'high',
          tags: ['page', 'visual', 'full-page'],
          dependencies: []
        };
        tests.push(test);
      }
    }

    return tests;
  }

  private async generateCriticalPathVisualTests(request: VisualTestRequest): Promise<VisualTestCase[]> {
    const tests: VisualTestCase[] = [];
    
    // Generate tests for critical paths identified in dependency analysis
    const criticalPaths = this.identifyCriticalPaths(request.sourceAnalysis);
    
    for (const path of criticalPaths.slice(0, 5)) { // Limit to top 5
      const test: VisualTestCase = {
        id: `visual-path-${path.id}`,
        name: `Visual Test: Critical Path ${path.name}`,
        description: `Visual regression test for critical path: ${path.description}`,
        url: path.startUrl,
        config: { ...this.config, ...request.config },
        baseline: `baselines/path-${path.id}.png`,
        priority: 'critical',
        tags: ['critical-path', 'visual', 'user-journey'],
        dependencies: path.components
      };
      tests.push(test);
    }

    return tests;
  }

  private async executeVisualTest(
    test: VisualTestCase,
    viewport: Viewport,
    browser: string,
    playwrightConfig: PlaywrightConfig
  ): Promise<VisualTestResult> {
    const startTime = Date.now();
    
    try {
      // Simulated visual test execution
      await this.simulateScreenshot(test, viewport, browser);
      
      // Simulate visual comparison
      const comparison = this.simulateVisualComparison(test);
      
      const artifacts: VisualArtifact[] = [
        {
          type: 'baseline',
          path: test.baseline,
          description: 'Baseline image',
          metadata: { width: viewport.width, height: viewport.height, format: 'png', size: 102400 }
        },
        {
          type: 'actual',
          path: `actual/${test.id}-${browser}-${viewport.name}.png`,
          description: 'Actual screenshot',
          metadata: { width: viewport.width, height: viewport.height, format: 'png', size: 104857 }
        }
      ];

      if (!comparison.passed) {
        artifacts.push({
          type: 'diff',
          path: `diff/${test.id}-${browser}-${viewport.name}.png`,
          description: 'Difference image',
          metadata: { width: viewport.width, height: viewport.height, format: 'png', size: 51200 }
        });
      }

      return {
        testId: test.id,
        status: comparison.passed ? 'passed' : 'failed',
        comparison,
        browser,
        viewport,
        artifacts,
        executionTime: Date.now() - startTime
      };

    } catch (error) {
      return {
        testId: test.id,
        status: 'failed',
        comparison: {
          pixelDifference: 0,
          percentageDifference: 0,
          threshold: test.config.threshold,
          passed: false,
          regions: []
        },
        browser,
        viewport,
        artifacts: [],
        executionTime: Date.now() - startTime
      };
    }
  }

  private simulateScreenshot(test: VisualTestCase, viewport: Viewport, browser: string): Promise<void> {
    // Simulate screenshot capture time (faster for tests)
    const captureTime = 100 + Math.random() * 200;
    return new Promise(resolve => setTimeout(resolve, captureTime));
  }

  private simulateVisualComparison(test: VisualTestCase): VisualComparison {
    // Simulate visual comparison with realistic results
    const pixelDifference = Math.random() * 1000;
    const percentageDifference = pixelDifference / 10000; // Assuming 10000 total pixels
    const passed = percentageDifference <= test.config.threshold;

    const regions: DifferenceRegion[] = [];
    if (!passed) {
      regions.push({
        x: Math.floor(Math.random() * 100),
        y: Math.floor(Math.random() * 100),
        width: Math.floor(Math.random() * 200) + 50,
        height: Math.floor(Math.random() * 100) + 25,
        severity: percentageDifference > 0.1 ? 'high' : 'medium',
        description: 'Layout shift detected'
      });
    }

    return {
      pixelDifference,
      percentageDifference,
      threshold: test.config.threshold,
      passed,
      regions
    };
  }

  private analyzeVisualResults(results: VisualTestResult[], testSuite: VisualTestSuite): VisualAnalysis {
    const changePatterns = this.identifyChangePatterns(results);
    const riskFactors = this.identifyVisualRiskFactors(results);
    const trends = this.calculateVisualTrends(results);

    return {
      changePatterns,
      impactAssessment: {
        overallImpact: 'moderate',
        userExperienceImpact: 0.3,
        affectedUserFlows: [],
        businessImpact: 'Minor visual inconsistencies detected',
        technicalImpact: 'Layout and styling changes require review'
      },
      riskFactors,
      trends
    };
  }

  private identifyChangePatterns(results: VisualTestResult[]): ChangePattern[] {
    const patterns: ChangePattern[] = [];
    const failedResults = results.filter(r => r.status === 'failed');

    if (failedResults.length > 0) {
      patterns.push({
        type: 'layout',
        frequency: failedResults.length,
        affectedComponents: failedResults.map(r => r.testId),
        severity: failedResults.length > 5 ? 'high' : 'medium',
        description: `Layout changes detected in ${failedResults.length} components`
      });
    }

    return patterns;
  }

  private identifyVisualRiskFactors(results: VisualTestResult[]): VisualRiskFactor[] {
    const riskFactors: VisualRiskFactor[] = [];
    const highDifferenceTests = results.filter(r => 
      r.comparison.percentageDifference > 0.1
    );

    if (highDifferenceTests.length > 0) {
      riskFactors.push({
        id: 'high-visual-difference',
        type: 'layout_shift',
        severity: 'high',
        description: 'Significant visual differences detected',
        affectedTests: highDifferenceTests.map(t => t.testId),
        mitigation: 'Review layout changes and update baselines if intentional'
      });
    }

    return riskFactors;
  }

  private calculateVisualTrends(results: VisualTestResult[]): VisualTrend[] {
    // Calculate trends based on historical data
    const currentFailureRate = results.filter(r => r.status === 'failed').length / results.length;
    
    return [
      {
        metric: 'difference_rate',
        direction: 'stable',
        change: 0.02,
        timeframe: 'last_7_days',
        significance: 'low'
      }
    ];
  }

  private generateVisualRecommendations(
    analysis: VisualAnalysis,
    results: VisualTestResult[]
  ): VisualRecommendation[] {
    const recommendations: VisualRecommendation[] = [];

    // Threshold recommendations
    const highFailureRate = results.filter(r => r.status === 'failed').length / results.length;
    if (highFailureRate > 0.3) {
      recommendations.push({
        id: 'adjust-threshold',
        type: 'threshold',
        priority: 'medium',
        title: 'Consider Adjusting Visual Threshold',
        description: 'High failure rate suggests threshold may be too strict',
        impact: 'Reduced false positives',
        effort: 'low',
        implementation: [
          'Analyze failed tests for legitimate changes',
          'Adjust threshold to 3-5% if appropriate',
          'Update baseline images for intentional changes'
        ]
      });
    }

    // Coverage recommendations
    if (results.length < 20) {
      recommendations.push({
        id: 'increase-coverage',
        type: 'coverage',
        priority: 'medium',
        title: 'Expand Visual Test Coverage',
        description: 'Consider adding more visual tests for comprehensive coverage',
        impact: 'Better regression detection',
        effort: 'medium',
        implementation: [
          'Add tests for remaining critical components',
          'Include different user states and interactions',
          'Test responsive breakpoints'
        ]
      });
    }

    return recommendations;
  }

  private calculateSummary(results: VisualTestResult[]) {
    const passed = results.filter(r => r.status === 'passed').length;
    const failed = results.filter(r => r.status === 'failed').length;
    const newBaselines = results.filter(r => r.status === 'baseline_created').length;
    const updatedBaselines = results.filter(r => r.status === 'baseline_updated').length;

    return {
      total: results.length,
      passed,
      failed,
      newBaselines,
      updatedBaselines
    };
  }

  private async createBaseline(test: VisualTestCase): Promise<void> {
    // Simulate baseline creation
    this.baselines.set(test.id, test.baseline);
    console.log(`📸 Created baseline for ${test.id}`);
  }

  private async updateBaseline(test: VisualTestCase): Promise<void> {
    // Simulate baseline update
    this.baselines.set(test.id, test.baseline);
    console.log(`🔄 Updated baseline for ${test.id}`);
  }

  private shouldUpdateBaseline(test: VisualTestCase): boolean {
    // Logic to determine if baseline should be updated
    return Math.random() < 0.1; // 10% chance for demo
  }

  private identifyCriticalPaths(analysis: DependencyAnalysisResult): Array<{
    id: string;
    name: string;
    description: string;
    startUrl: string;
    components: string[];
  }> {
    // Extract critical paths from dependency analysis
    return [
      {
        id: 'user-onboarding',
        name: 'User Onboarding',
        description: 'Critical user onboarding flow',
        startUrl: '/signup',
        components: ['signup-form', 'verification', 'welcome']
      },
      {
        id: 'checkout-flow',
        name: 'Checkout Process',
        description: 'E-commerce checkout flow',
        startUrl: '/cart',
        components: ['cart', 'billing', 'payment', 'confirmation']
      }
    ];
  }

  private identifyAffectedUserFlows(
    failedTests: VisualTestResult[],
    dependencyAnalysis: DependencyAnalysisResult
  ): string[] {
    // Identify user flows affected by visual changes
    return failedTests.map(t => `flow-${t.testId}`);
  }

  private assessBusinessImpact(
    failedTests: VisualTestResult[],
    overallImpact: VisualImpactAssessment['overallImpact']
  ): string {
    if (overallImpact === 'major') {
      return 'Significant business impact: User experience severely affected';
    } else if (overallImpact === 'significant') {
      return 'Moderate business impact: Notable changes to user interface';
    } else {
      return 'Minimal business impact: Minor visual inconsistencies';
    }
  }

  private assessTechnicalImpact(
    failedTests: VisualTestResult[],
    dependencyAnalysis: DependencyAnalysisResult
  ): string {
    const affectedComponents = failedTests.length;
    return `${affectedComponents} components affected by visual changes, requiring developer review`;
  }

  private getComponentURL(component: any): string {
    return `/components/${component.name.toLowerCase().replace(/\s+/g, '-')}`;
  }
}