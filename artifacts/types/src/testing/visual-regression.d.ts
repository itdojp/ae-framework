/**
 * Visual Regression Testing System for Phase 3.2
 * Provides automated visual testing and change detection
 */
import { EventEmitter } from 'events';
import type { DependencyAnalysisResult } from '../analysis/dependency-analyzer.js';
import type { PlaywrightConfig } from './playwright-integration.js';
export interface VisualTestConfig {
    threshold: number;
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
    selector?: string;
    config: VisualTestConfig;
    baseline: string;
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
    userExperienceImpact: number;
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
export declare class VisualRegressionTesting extends EventEmitter {
    private config;
    private activeTests;
    private baselines;
    private testHistory;
    constructor(config?: Partial<VisualTestConfig>);
    /**
     * Generate visual tests from dependency analysis
     */
    generateVisualTests(request: VisualTestRequest): Promise<VisualTestSuite>;
    /**
     * Execute visual regression tests
     */
    executeVisualTests(testSuite: VisualTestSuite, playwrightConfig: PlaywrightConfig): Promise<VisualRegressionReport>;
    /**
     * Create or update baseline images
     */
    manageBaselines(testSuite: VisualTestSuite, mode: 'create' | 'update' | 'selective'): Promise<{
        created: number;
        updated: number;
        skipped: number;
    }>;
    /**
     * Analyze visual changes and their impact
     */
    analyzeVisualChanges(results: VisualTestResult[], dependencyAnalysis: DependencyAnalysisResult): VisualImpactAssessment;
    private createDefaultConfig;
    private setupEventHandlers;
    private generateComponentVisualTests;
    private generatePageVisualTests;
    private generateCriticalPathVisualTests;
    private executeVisualTest;
    private simulateScreenshot;
    private simulateVisualComparison;
    private analyzeVisualResults;
    private identifyChangePatterns;
    private identifyVisualRiskFactors;
    private calculateVisualTrends;
    private generateVisualRecommendations;
    private calculateSummary;
    private createBaseline;
    private updateBaseline;
    private shouldUpdateBaseline;
    private identifyCriticalPaths;
    private identifyAffectedUserFlows;
    private assessBusinessImpact;
    private assessTechnicalImpact;
    private extractComponentName;
    private getComponentURL;
}
