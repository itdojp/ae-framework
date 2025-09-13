/**
 * Intelligent Test Selection System for Phase 3.2
 * AI-driven test selection with risk analysis and optimization
 */

import { EventEmitter } from 'events';
import type { SequentialInferenceEngine, ComplexQuery } from '../engines/sequential-inference-engine.js';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';

// Core interfaces
export interface CodeChange {
  id: string;
  type: 'addition' | 'modification' | 'deletion';
  filePath: string;
  componentId: string;
  impact: 'low' | 'medium' | 'high';
  changeType: 'logic' | 'config' | 'interface' | 'test' | 'feature';
  linesChanged: number;
  additions: number;
  deletions: number;
  riskScore: number;
  description: string;
}

export interface TestCase {
  id: string;
  name: string;
  type: 'unit' | 'integration' | 'e2e';
  filePath: string;
  componentCoverage: string[];
  priority: 'critical' | 'high' | 'medium' | 'low';
  executionTime: number;
  lastRun: Date;
  successRate: number;
  tags: string[];
}

export interface TestSuite {
  id: string;
  name: string;
  type: 'unit' | 'integration' | 'e2e';
  tests: TestCase[];
}

export interface TestInventory {
  id: string;
  timestamp: Date;
  totalTests: number;
  testSuites: TestSuite[];
  coverage: {
    overall: number;
    byComponent: Record<string, number>;
    byTestType: Record<string, number>;
  };
  metrics: {
    avgExecutionTime: number;
    flakyTests: number;
    recentFailures: number;
  };
}

export interface TestSelectionRequest {
  id: string;
  changes: CodeChange[];
  testInventory: TestInventory;
  dependencyAnalysis: DependencyAnalysisResult;
  constraints: {
    maxExecutionTime: number;
    maxTests: number;
    minCoverage: number;
    budgetLimits: {
      timePerTest: number;
      totalBudget: number;
    };
  };
  strategy: 'risk_based' | 'coverage_optimized' | 'balanced' | 'ml_optimized';
  preferences: {
    prioritizeRecentChanges: boolean;
    includeFlakyTests: boolean;
    parallelExecution: boolean;
    regressionFocus: boolean;
  };
}

export interface SelectedTestSuite {
  id: string;
  name: string;
  tests: TestCase[];
  totalTests: number;
  estimatedExecutionTime: number;
  coverageProjection: number;
}

export interface SelectionReasoning {
  strategy: string;
  factors: Array<{
    name: string;
    weight: number;
    description: string;
    impact: 'high' | 'medium' | 'low';
  }>;
  tradeoffs: Array<{
    decision: string;
    rationale: string;
    alternativeConsidered: string;
  }>;
  confidence: number;
}

export interface TestSelectionResult {
  requestId: string;
  selectedTests: SelectedTestSuite;
  reasoning: SelectionReasoning;
  optimization: {
    parallelizationGains: number;
    recommendations: string[];
    potentialSavings: number;
  };
  recommendations: string[];
}

export interface CoverageAnalysisResult {
  overallCoverage: number;
  componentCoverage: Record<string, number>;
  riskCoverage: Record<string, number>;
  gaps: Array<{
    type: 'component' | 'path' | 'scenario';
    severity: 'high' | 'medium' | 'low';
    description: string;
    impact: string;
  }>;
  recommendations: Array<{
    type: string;
    priority: 'high' | 'medium' | 'low';
    description: string;
    effort: 'high' | 'medium' | 'low';
    impact: string;
  }>;
  projectedCoverage: Record<string, number>;
}

export interface ExecutionTimePrediction {
  estimatedTime: number;
  confidence: number;
  breakdown: {
    sequential: number;
    parallel: number;
    overhead: number;
  };
  factors: Array<{
    name: string;
    impact: number;
    description: string;
  }>;
  optimization: {
    parallelizationGains: number;
    recommendations: string[];
    potentialSavings: number;
  };
}

// Configuration interface
export interface IntelligentTestSelectionConfig {
  riskThreshold: number;
  maxTestsPerComponent: number;
  enableMLPrediction: boolean;
  cacheEnabled: boolean;
  parallelExecutionEnabled: boolean;
}

/**
 * Analyzes code changes and assesses their impact on testing requirements
 */
class ChangeAnalyzer {
  analyzeChanges(changes: CodeChange[], dependencyGraph: DependencyAnalysisResult): Map<string, number> {
    const impactMap = new Map<string, number>();
    
    for (const change of changes) {
      let impact = this.calculateBaseImpact(change);
      
      // Amplify impact based on dependency connections
      const dependencies = this.findDependencies(change.componentId, dependencyGraph);
      impact *= (1 + dependencies.length * 0.2);
      
      // Consider change type
      const typeMultiplier = this.getChangeTypeMultiplier(change.changeType);
      impact *= typeMultiplier;
      
      impactMap.set(change.componentId, Math.min(1.0, impact));
    }
    
    return impactMap;
  }
  
  private calculateBaseImpact(change: CodeChange): number {
    const baseImpact = {
      'low': 0.3,
      'medium': 0.6,
      'high': 0.9
    }[change.impact];
    
    // Factor in risk score
    return (baseImpact + change.riskScore) / 2;
  }
  
  private findDependencies(componentId: string, graph: DependencyAnalysisResult): string[] {
    const node = graph.nodes.find(n => n.id === componentId);
    return node?.dependencies || [];
  }
  
  private getChangeTypeMultiplier(changeType: string): number {
    const multipliers = {
      'logic': 1.2,
      'interface': 1.1,
      'config': 0.8,
      'test': 0.7,
      'feature': 1.0
    };
    return multipliers[changeType as keyof typeof multipliers] || 1.0;
  }
}

/**
 * Assesses risk levels for different components and test scenarios
 */
class RiskAssessor {
  assessRisk(
    changes: CodeChange[], 
    testInventory: TestInventory, 
    dependencyAnalysis: DependencyAnalysisResult
  ): Map<string, number> {
    const riskMap = new Map<string, number>();
    
    // Analyze each component's risk
    for (const change of changes) {
      let risk = change.riskScore;
      
      // Factor in test coverage
      const coverage = testInventory.coverage.byComponent[change.componentId] || 0;
      risk *= (1 + (1 - coverage)); // Higher risk for lower coverage
      
      // Factor in recent failures
      const failureRate = this.calculateFailureRate(change.componentId, testInventory);
      risk *= (1 + failureRate);
      
      // Factor in complexity from dependency analysis
      const complexity = this.getComplexityScore(change.componentId, dependencyAnalysis);
      risk *= (1 + complexity * 0.3);
      
      riskMap.set(change.componentId, Math.min(1.0, risk));
    }
    
    return riskMap;
  }
  
  private calculateFailureRate(componentId: string, inventory: TestInventory): number {
    const relevantTests = this.findTestsForComponent(componentId, inventory);
    if (relevantTests.length === 0) return 0.5; // Default high risk for untested components
    
    const avgSuccessRate = relevantTests.reduce((sum, test) => sum + test.successRate, 0) / relevantTests.length;
    return 1 - avgSuccessRate;
  }
  
  private findTestsForComponent(componentId: string, inventory: TestInventory): TestCase[] {
    const tests: TestCase[] = [];
    for (const suite of inventory.testSuites) {
      for (const test of suite.tests) {
        if (test.componentCoverage.includes(componentId)) {
          tests.push(test);
        }
      }
    }
    return tests;
  }
  
  private getComplexityScore(componentId: string, analysis: DependencyAnalysisResult): number {
    const node = analysis.nodes.find(n => n.id === componentId);
    if (!node?.metadata?.['complexity']) return 0.5;
    return Math.min(1.0, (node.metadata['complexity'] as number) / 10);
  }
}

/**
 * Main test selection engine with multiple strategies
 */
class SelectionEngine {
  selectTests(
    request: TestSelectionRequest,
    riskScores: Map<string, number>,
    impactScores: Map<string, number>
  ): { tests: TestCase[], reasoning: SelectionReasoning } {
    const strategy = request.strategy;
    let selectedTests: TestCase[] = [];
    let reasoning: SelectionReasoning;
    
    switch (strategy) {
      case 'risk_based':
        ({ tests: selectedTests, reasoning } = this.riskBasedSelection(request, riskScores));
        break;
      case 'coverage_optimized':
        ({ tests: selectedTests, reasoning } = this.coverageOptimizedSelection(request, impactScores));
        break;
      case 'balanced':
        ({ tests: selectedTests, reasoning } = this.balancedSelection(request, riskScores, impactScores));
        break;
      case 'ml_optimized':
        ({ tests: selectedTests, reasoning } = this.mlOptimizedSelection(request, riskScores, impactScores));
        break;
      default:
        ({ tests: selectedTests, reasoning } = this.balancedSelection(request, riskScores, impactScores));
    }
    
    // Apply constraints
    selectedTests = this.applyConstraints(selectedTests, request.constraints);
    
    return { tests: selectedTests, reasoning };
  }
  
  private riskBasedSelection(
    request: TestSelectionRequest, 
    riskScores: Map<string, number>
  ): { tests: TestCase[], reasoning: SelectionReasoning } {
    const allTests = this.getAllTests(request.testInventory);
    const scoredTests = allTests.map(test => ({
      test,
      score: this.calculateRiskScore(test, riskScores)
    }));
    
    scoredTests.sort((a, b) => b.score - a.score);
    
    return {
      tests: scoredTests.slice(0, request.constraints.maxTests).map(item => item.test),
      reasoning: {
        strategy: 'risk_based',
        factors: [
          { name: 'Risk Assessment', weight: 0.8, description: 'Prioritized high-risk components', impact: 'high' },
          { name: 'Component Coverage', weight: 0.2, description: 'Ensured adequate test coverage', impact: 'medium' }
        ],
        tradeoffs: [
          { 
            decision: 'Prioritize risk over coverage', 
            rationale: 'Risk-based strategy focuses on preventing failures', 
            alternativeConsidered: 'Balanced coverage approach' 
          }
        ],
        confidence: 0.85
      }
    };
  }
  
  private coverageOptimizedSelection(
    request: TestSelectionRequest, 
    impactScores: Map<string, number>
  ): { tests: TestCase[], reasoning: SelectionReasoning } {
    const allTests = this.getAllTests(request.testInventory);
    const selectedTests: TestCase[] = [];
    const coveredComponents = new Set<string>();
    
    // Greedy selection for maximum coverage
    while (selectedTests.length < request.constraints.maxTests && selectedTests.length < allTests.length) {
      let bestTest: TestCase | null = null;
      let bestScore = -1;
      
      for (const test of allTests) {
        if (selectedTests.includes(test)) continue;
        
        const newCoverage = test.componentCoverage.filter(comp => !coveredComponents.has(comp)).length;
        const impactWeight = test.componentCoverage.reduce((sum, comp) => sum + (impactScores.get(comp) || 0), 0);
        const score = newCoverage * 10 + impactWeight;
        
        if (score > bestScore) {
          bestScore = score;
          bestTest = test;
        }
      }
      
      if (bestTest) {
        selectedTests.push(bestTest);
        bestTest.componentCoverage.forEach(comp => coveredComponents.add(comp));
      } else {
        break;
      }
    }
    
    return {
      tests: selectedTests,
      reasoning: {
        strategy: 'coverage_optimized',
        factors: [
          { name: 'Component Coverage', weight: 0.7, description: 'Maximized component coverage', impact: 'high' },
          { name: 'Change Impact', weight: 0.3, description: 'Weighted by change impact', impact: 'medium' }
        ],
        tradeoffs: [
          { 
            decision: 'Maximize coverage over execution time', 
            rationale: 'Coverage strategy prioritizes comprehensive testing', 
            alternativeConsidered: 'Time-optimized selection' 
          }
        ],
        confidence: 0.78
      }
    };
  }
  
  private balancedSelection(
    request: TestSelectionRequest,
    riskScores: Map<string, number>,
    impactScores: Map<string, number>
  ): { tests: TestCase[], reasoning: SelectionReasoning } {
    const allTests = this.getAllTests(request.testInventory);
    const scoredTests = allTests.map(test => {
      const riskScore = this.calculateRiskScore(test, riskScores);
      const impactScore = this.calculateImpactScore(test, impactScores);
      const timeScore = this.calculateTimeScore(test, request.constraints.maxExecutionTime);
      
      // Balanced weighting
      const combinedScore = (riskScore * 0.4) + (impactScore * 0.4) + (timeScore * 0.2);
      
      return { test, score: combinedScore };
    });
    
    scoredTests.sort((a, b) => b.score - a.score);
    
    return {
      tests: scoredTests.slice(0, request.constraints.maxTests).map(item => item.test),
      reasoning: {
        strategy: 'balanced',
        factors: [
          { name: 'Risk Assessment', weight: 0.4, description: 'Balanced risk consideration', impact: 'high' },
          { name: 'Impact Analysis', weight: 0.4, description: 'Change impact evaluation', impact: 'high' },
          { name: 'Execution Time', weight: 0.2, description: 'Time constraint optimization', impact: 'medium' }
        ],
        tradeoffs: [
          { 
            decision: 'Balance multiple factors', 
            rationale: 'Balanced approach considers risk, impact, and time', 
            alternativeConsidered: 'Single-factor optimization' 
          }
        ],
        confidence: 0.82
      }
    };
  }
  
  private mlOptimizedSelection(
    request: TestSelectionRequest,
    riskScores: Map<string, number>,
    impactScores: Map<string, number>
  ): { tests: TestCase[], reasoning: SelectionReasoning } {
    // Simplified ML approach - in reality would use trained models
    const allTests = this.getAllTests(request.testInventory);
    const scoredTests = allTests.map(test => {
      const features = this.extractFeatures(test, riskScores, impactScores, request);
      const mlScore = this.calculateMLScore(features);
      
      return { test, score: mlScore };
    });
    
    scoredTests.sort((a, b) => b.score - a.score);
    
    return {
      tests: scoredTests.slice(0, request.constraints.maxTests).map(item => item.test),
      reasoning: {
        strategy: 'ml_optimized',
        factors: [
          { name: 'ML Feature Analysis', weight: 0.6, description: 'Machine learning feature weighting', impact: 'high' },
          { name: 'Historical Performance', weight: 0.3, description: 'Past test effectiveness', impact: 'medium' },
          { name: 'Adaptive Learning', weight: 0.1, description: 'Continuous model improvement', impact: 'low' }
        ],
        tradeoffs: [
          { 
            decision: 'Use ML predictions over heuristics', 
            rationale: 'ML models learn from historical data patterns', 
            alternativeConsidered: 'Rule-based selection' 
          }
        ],
        confidence: 0.88
      }
    };
  }
  
  private getAllTests(inventory: TestInventory): TestCase[] {
    const allTests: TestCase[] = [];
    for (const suite of inventory.testSuites) {
      allTests.push(...suite.tests);
    }
    return allTests;
  }
  
  private calculateRiskScore(test: TestCase, riskScores: Map<string, number>): number {
    return test.componentCoverage.reduce((sum, comp) => {
      return sum + (riskScores.get(comp) || 0);
    }, 0) / test.componentCoverage.length;
  }
  
  private calculateImpactScore(test: TestCase, impactScores: Map<string, number>): number {
    return test.componentCoverage.reduce((sum, comp) => {
      return sum + (impactScores.get(comp) || 0);
    }, 0) / test.componentCoverage.length;
  }
  
  private calculateTimeScore(test: TestCase, maxTime: number): number {
    // Favor faster tests
    return Math.max(0, 1 - (test.executionTime / maxTime));
  }
  
  private extractFeatures(test: TestCase, riskScores: Map<string, number>, impactScores: Map<string, number>, request: TestSelectionRequest): number[] {
    return [
      this.calculateRiskScore(test, riskScores),
      this.calculateImpactScore(test, impactScores),
      test.successRate,
      test.executionTime / 1000, // Normalize to seconds
      test.componentCoverage.length,
      this.getPriorityWeight(test.priority)
    ];
  }
  
  private calculateMLScore(features: number[]): number {
    // Simplified ML scoring - in reality would use trained weights
    const weights = [0.3, 0.25, 0.2, -0.1, 0.1, 0.15];
    return features.reduce((sum, feature, i) => sum + feature * (weights[i] || 0), 0);
  }
  
  private getPriorityWeight(priority: string): number {
    const weights = { 'critical': 1.0, 'high': 0.8, 'medium': 0.6, 'low': 0.4 };
    return weights[priority as keyof typeof weights] || 0.5;
  }
  
  private applyConstraints(tests: TestCase[], constraints: TestSelectionRequest['constraints']): TestCase[] {
    let filteredTests = tests.slice();
    
    // Apply execution time constraint
    let totalTime = 0;
    filteredTests = filteredTests.filter(test => {
      if (totalTime + test.executionTime <= constraints.maxExecutionTime) {
        totalTime += test.executionTime;
        return true;
      }
      return false;
    });
    
    // Apply max tests constraint
    if (filteredTests.length > constraints.maxTests) {
      filteredTests = filteredTests.slice(0, constraints.maxTests);
    }
    
    return filteredTests;
  }
}

/**
 * Analyzes test coverage and identifies gaps
 */
class CoverageAnalyzer {
  analyzeCoverage(changes: CodeChange[], testInventory: TestInventory): CoverageAnalysisResult {
    const componentCoverage = this.calculateComponentCoverage(changes, testInventory);
    const riskCoverage = this.calculateRiskCoverage(changes, testInventory);
    const gaps = this.identifyGaps(changes, testInventory);
    const recommendations = this.generateRecommendations(gaps);
    
    return {
      overallCoverage: this.calculateOverallCoverage(componentCoverage),
      componentCoverage,
      riskCoverage,
      gaps,
      recommendations,
      projectedCoverage: this.projectCoverage(componentCoverage, recommendations)
    };
  }
  
  private calculateComponentCoverage(changes: CodeChange[], inventory: TestInventory): Record<string, number> {
    const coverage: Record<string, number> = {};
    
    for (const change of changes) {
      coverage[change.componentId] = inventory.coverage.byComponent[change.componentId] || 0;
    }
    
    return coverage;
  }
  
  private calculateRiskCoverage(changes: CodeChange[], inventory: TestInventory): Record<string, number> {
    const riskCoverage: Record<string, number> = {};
    
    for (const change of changes) {
      const tests = this.findTestsForComponent(change.componentId, inventory);
      const highPriorityTests = tests.filter(t => ['critical', 'high'].includes(t.priority));
      
      riskCoverage[change.componentId] = tests.length > 0 
        ? highPriorityTests.length / tests.length 
        : 0;
    }
    
    return riskCoverage;
  }
  
  private identifyGaps(changes: CodeChange[], inventory: TestInventory) {
    const gaps = [];
    
    for (const change of changes) {
      const coverage = inventory.coverage.byComponent[change.componentId] || 0;
      
      // Always identify some gaps for testing - check if coverage exists at all
      if (coverage === 0) {
        gaps.push({
          type: 'component' as const,
          severity: 'high' as const,
          description: `No test coverage for ${change.componentId}`,
          impact: 'High risk of undetected issues'
        });
      } else if (coverage < 0.5) {
        gaps.push({
          type: 'component' as const,
          severity: 'medium' as const,
          description: `Low test coverage for ${change.componentId}`,
          impact: 'Moderate risk of undetected issues'
        });
      }
      
      if (change.riskScore > 0.7 && coverage < 0.8) {
        gaps.push({
          type: 'scenario' as const,
          severity: 'high' as const,
          description: `High-risk change with insufficient coverage`,
          impact: 'Critical functionality may be untested'
        });
      }
      
      // Check for missing path coverage
      if (change.changeType === 'logic' && coverage < 0.9) {
        gaps.push({
          type: 'path' as const,
          severity: 'medium' as const,
          description: `Logic change may require additional path coverage`,
          impact: 'Some code paths may remain untested'
        });
      }
    }
    
    return gaps;
  }
  
  private generateRecommendations(gaps: any[]) {
    return gaps.map(gap => ({
      type: 'test-coverage',
      priority: gap.severity as 'high' | 'medium' | 'low',
      description: `Address ${gap.description.toLowerCase()}`,
      effort: 'medium' as const,
      impact: 'Improved test coverage and risk mitigation'
    }));
  }
  
  private calculateOverallCoverage(componentCoverage: Record<string, number>): number {
    const values = Object.values(componentCoverage);
    return values.length > 0 ? values.reduce((sum, val) => sum + val, 0) / values.length : 0;
  }
  
  private projectCoverage(current: Record<string, number>, recommendations: any[]): Record<string, number> {
    const projected = { ...current };
    
    // Simulate coverage improvement from recommendations
    for (const [component, coverage] of Object.entries(projected)) {
      const relevantRecs = recommendations.filter(r => r.description.includes(component));
      if (relevantRecs.length > 0) {
        projected[component] = Math.min(1.0, coverage + 0.2);
      }
    }
    
    return projected;
  }
  
  private findTestsForComponent(componentId: string, inventory: TestInventory): TestCase[] {
    const tests: TestCase[] = [];
    for (const suite of inventory.testSuites) {
      for (const test of suite.tests) {
        if (test.componentCoverage.includes(componentId)) {
          tests.push(test);
        }
      }
    }
    return tests;
  }
}

/**
 * Predicts test execution times with optimization suggestions
 */
class TimePredictor {
  predictExecutionTime(tests: SelectedTestSuite): ExecutionTimePrediction {
    const sequential = this.calculateSequentialTime(tests.tests);
    const parallel = this.calculateParallelTime(tests.tests);
    const overhead = this.calculateOverhead(tests.tests);
    
    const factors = this.identifyTimeFactors(tests.tests);
    const optimization = this.generateOptimizations(tests.tests, sequential, parallel);
    
    return {
      estimatedTime: parallel + overhead,
      confidence: 0.85,
      breakdown: { sequential, parallel, overhead },
      factors,
      optimization
    };
  }
  
  private calculateSequentialTime(tests: TestCase[]): number {
    return tests.reduce((sum, test) => sum + test.executionTime, 0);
  }
  
  private calculateParallelTime(tests: TestCase[]): number {
    // Simplified parallel calculation - assumes perfect parallelization
    const maxTime = Math.max(...tests.map(t => t.executionTime));
    const avgTime = tests.reduce((sum, test) => sum + test.executionTime, 0) / tests.length;
    
    // Reality factor - not all tests can run perfectly in parallel
    return Math.max(maxTime, avgTime * 0.6);
  }
  
  private calculateOverhead(tests: TestCase[]): number {
    // Setup/teardown overhead
    const baseOverhead = 100; // Base overhead in ms
    const perTestOverhead = tests.length * 10; // Per test overhead
    return baseOverhead + perTestOverhead;
  }
  
  private identifyTimeFactors(tests: TestCase[]) {
    const factors = [];
    
    const integrationTests = tests.filter(t => t.type === 'integration').length;
    if (integrationTests > 0) {
      factors.push({
        name: 'Integration Tests',
        impact: integrationTests * 0.3,
        description: `${integrationTests} integration tests require additional setup time`
      });
    }
    
    const e2eTests = tests.filter(t => t.type === 'e2e').length;
    if (e2eTests > 0) {
      factors.push({
        name: 'E2E Tests',
        impact: e2eTests * 0.5,
        description: `${e2eTests} end-to-end tests are time-intensive`
      });
    }
    
    return factors;
  }
  
  private generateOptimizations(tests: TestCase[], sequential: number, parallel: number): {
    parallelizationGains: number;
    recommendations: string[];
    potentialSavings: number;
  } {
    const parallelizationGains = (sequential - parallel) / sequential;
    const recommendations = [];
    
    if (parallelizationGains > 0.3) {
      recommendations.push('Enable parallel test execution');
    }
    
    const slowTests = tests.filter(t => t.executionTime > 5000);
    if (slowTests.length > 0) {
      recommendations.push(`Optimize ${slowTests.length} slow-running tests`);
    }
    
    const flakyTests = tests.filter(t => t.successRate < 0.9);
    if (flakyTests.length > 0) {
      recommendations.push(`Stabilize ${flakyTests.length} flaky tests`);
    }
    
    return {
      parallelizationGains,
      recommendations,
      potentialSavings: sequential - parallel
    };
  }
}

/**
 * Main Intelligent Test Selection class that orchestrates the entire system
 */
export class IntelligentTestSelection extends EventEmitter {
  private changeAnalyzer: ChangeAnalyzer;
  private riskAssessor: RiskAssessor;
  private selectionEngine: SelectionEngine;
  private coverageAnalyzer: CoverageAnalyzer;
  private timePredictor: TimePredictor;
  private inferenceEngine: SequentialInferenceEngine;
  private config: IntelligentTestSelectionConfig;
  
  constructor(
    inferenceEngine: SequentialInferenceEngine, 
    config: Partial<IntelligentTestSelectionConfig> = {}
  ) {
    super();
    
    this.inferenceEngine = inferenceEngine;
    this.config = {
      riskThreshold: 0.7,
      maxTestsPerComponent: 10,
      enableMLPrediction: true,
      cacheEnabled: true,
      parallelExecutionEnabled: true,
      ...config
    };
    
    this.changeAnalyzer = new ChangeAnalyzer();
    this.riskAssessor = new RiskAssessor();
    this.selectionEngine = new SelectionEngine();
    this.coverageAnalyzer = new CoverageAnalyzer();
    this.timePredictor = new TimePredictor();
  }
  
  async selectTests(request: TestSelectionRequest): Promise<TestSelectionResult> {
    this.emit('testSelectionStarted', request);
    
    try {
      // Step 1: Analyze changes and their impact
      const impactScores = this.changeAnalyzer.analyzeChanges(request.changes, request.dependencyAnalysis);
      
      // Step 2: Assess risk levels
      const riskScores = this.riskAssessor.assessRisk(
        request.changes, 
        request.testInventory, 
        request.dependencyAnalysis
      );
      
      // Step 3: Use inference engine for complex decision making
      if (request.strategy === 'ml_optimized' && this.config.enableMLPrediction) {
        await this.enhanceWithInferenceEngine(request, riskScores, impactScores);
      }
      
      // Step 4: Select tests using appropriate strategy
      const { tests, reasoning } = this.selectionEngine.selectTests(request, riskScores, impactScores);
      
      // Step 5: Create selected test suite
      const selectedTests: SelectedTestSuite = {
        id: `selection-${Date.now()}`,
        name: `${request.strategy} Test Selection`,
        tests,
        totalTests: tests.length,
        estimatedExecutionTime: tests.reduce((sum, test) => sum + test.executionTime, 0),
        coverageProjection: this.calculateCoverageProjection(tests, request.changes)
      };
      
      // Step 6: Generate optimization recommendations
      const timePrediction = this.timePredictor.predictExecutionTime(selectedTests);
      
      // Step 7: Create final result
      const result: TestSelectionResult = {
        requestId: request.id,
        selectedTests,
        reasoning,
        optimization: timePrediction.optimization,
        recommendations: this.generateRecommendations(selectedTests, request)
      };
      
      this.emit('testSelectionCompleted', result);
      return result;
      
    } catch (error) {
      this.emit('testSelectionFailed', error);
      throw error;
    }
  }
  
  async analyzeCoverage(changes: CodeChange[], testInventory: TestInventory): Promise<CoverageAnalysisResult> {
    this.emit('coverageAnalysisStarted', { changes, testInventory });
    
    const result = this.coverageAnalyzer.analyzeCoverage(changes, testInventory);
    
    this.emit('coverageAnalysisCompleted', result);
    return result;
  }
  
  predictExecutionTime(tests: SelectedTestSuite): ExecutionTimePrediction {
    return this.timePredictor.predictExecutionTime(tests);
  }
  
  private async enhanceWithInferenceEngine(
    request: TestSelectionRequest,
    riskScores: Map<string, number>,
    impactScores: Map<string, number>
  ): Promise<void> {
    const query: ComplexQuery = {
      id: `test-selection-${Date.now()}`,
      description: 'Intelligent test selection optimization query',
      context: {
        changes: request.changes,
        constraints: request.constraints,
        strategy: request.strategy,
        riskScores: Object.fromEntries(riskScores),
        impactScores: Object.fromEntries(impactScores)
      },
      constraints: [
        {
          type: 'resource' as const,
          condition: `execution_time <= ${request.constraints.maxExecutionTime}`,
          severity: 'critical' as const
        },
        {
          type: 'resource' as const,
          condition: `test_count <= ${request.constraints.maxTests}`,
          severity: 'error' as const
        }
      ],
      priority: 'high' as const,
      expectedOutcome: 'Optimized test selection with balanced risk and coverage'
    };
    
    const inferenceResult = await this.inferenceEngine.processComplexQuery(query);
    
    // Enhance scores based on inference engine recommendations
    if (inferenceResult.finalResult?.selectedTests) {
      // Apply ML insights to adjust scores
      this.applyMLInsights(inferenceResult, riskScores, impactScores);
    }
  }
  
  private applyMLInsights(
    inferenceResult: any,
    riskScores: Map<string, number>,
    impactScores: Map<string, number>
  ): void {
    // Apply ML-based adjustments to scores
    const confidence = inferenceResult.confidence || 0.8;
    const adjustmentFactor = confidence * 0.2;
    
    // Enhance high-confidence predictions
    for (const [component, score] of riskScores.entries()) {
      riskScores.set(component, Math.min(1.0, score + adjustmentFactor));
    }
  }
  
  private calculateCoverageProjection(tests: TestCase[], changes: CodeChange[]): number {
    const changedComponents = new Set(changes.map(c => c.componentId));
    const coveredComponents = new Set();
    
    for (const test of tests) {
      for (const component of test.componentCoverage) {
        if (changedComponents.has(component)) {
          coveredComponents.add(component);
        }
      }
    }
    
    return changedComponents.size > 0 ? coveredComponents.size / changedComponents.size : 1.0;
  }
  
  private generateRecommendations(selectedTests: SelectedTestSuite, request: TestSelectionRequest): string[] {
    const recommendations = [];
    
    if (selectedTests.estimatedExecutionTime > request.constraints.maxExecutionTime * 0.8) {
      recommendations.push('Consider enabling parallel execution to reduce total test time');
    }
    
    if (selectedTests.coverageProjection < 0.8) {
      recommendations.push('Coverage may be insufficient - consider adding more comprehensive tests');
    }
    
    const flakyTests = selectedTests.tests.filter(t => t.successRate < 0.9);
    if (flakyTests.length > 0) {
      recommendations.push(`${flakyTests.length} flaky tests detected - consider stabilizing before execution`);
    }
    
    return recommendations;
  }
}
