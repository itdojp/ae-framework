/**
 * Intelligent Test Selection System for Phase 3.2
 * AI-driven test selection with risk analysis and optimization
 */
import { EventEmitter } from 'events';
import type { SequentialInferenceEngine } from '../engines/sequential-inference-engine.js';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';
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
export interface IntelligentTestSelectionConfig {
    riskThreshold: number;
    maxTestsPerComponent: number;
    enableMLPrediction: boolean;
    cacheEnabled: boolean;
    parallelExecutionEnabled: boolean;
}
/**
 * Main Intelligent Test Selection class that orchestrates the entire system
 */
export declare class IntelligentTestSelection extends EventEmitter {
    private changeAnalyzer;
    private riskAssessor;
    private selectionEngine;
    private coverageAnalyzer;
    private timePredictor;
    private inferenceEngine;
    private config;
    constructor(inferenceEngine: SequentialInferenceEngine, config?: Partial<IntelligentTestSelectionConfig>);
    selectTests(request: TestSelectionRequest): Promise<TestSelectionResult>;
    analyzeCoverage(changes: CodeChange[], testInventory: TestInventory): Promise<CoverageAnalysisResult>;
    predictExecutionTime(tests: SelectedTestSuite): ExecutionTimePrediction;
    private enhanceWithInferenceEngine;
    private applyMLInsights;
    private calculateCoverageProjection;
    private generateRecommendations;
}
