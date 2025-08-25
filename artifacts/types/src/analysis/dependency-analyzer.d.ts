/**
 * Dependency Analyzer for Phase 3.1 Implementation
 * Analyzes project dependencies, module relationships, and impact scope
 */
import { EventEmitter } from 'events';
import type { DependencyGraph, ImpactAnalysis, DependencyNode } from '../engines/sequential-inference-engine.js';
export interface CircularDependency {
    id: string;
    cycle: string[];
    severity: 'warning' | 'error' | 'critical';
    description: string;
    suggestions: string[];
    affectedComponents: string[];
}
export interface DependencyAnalysisRequest {
    id: string;
    projectRoot: string;
    targetFiles?: string[];
    analysisScope: 'project' | 'module' | 'file' | 'function';
    includeExternal: boolean;
    maxDepth?: number;
    excludePatterns?: string[];
    analysisTypes: DependencyAnalysisType[];
}
export type DependencyAnalysisType = 'structural' | 'functional' | 'circular' | 'impact' | 'risk' | 'optimization' | 'security' | 'performance';
export interface DependencyAnalysisResult {
    requestId: string;
    graph: DependencyGraph;
    nodes: DependencyNode[];
    circularDependencies: CircularDependency[];
    metrics: DependencyMetrics;
    riskAssessment: DependencyRiskAssessment;
    recommendations: DependencyRecommendation[];
    impactAnalysis?: ImpactAnalysis;
    optimizationSuggestions: OptimizationSuggestion[];
}
export interface DependencyMetrics {
    totalNodes: number;
    totalEdges: number;
    averageDependencies: number;
    maxDependencyDepth: number;
    circularDependencyCount: number;
    criticalPathLength: number;
    modularityScore: number;
    cohesionScore: number;
    couplingScore: number;
    stabilityIndex: number;
}
export interface DependencyRiskAssessment {
    overallRisk: 'low' | 'medium' | 'high' | 'critical';
    riskFactors: RiskFactor[];
    vulnerabilities: Vulnerability[];
    mitigationPlan: MitigationStep[];
    contingencyActions: string[];
}
export interface RiskFactor {
    id: string;
    type: 'circular' | 'deep_nesting' | 'high_coupling' | 'single_point_failure' | 'external_dependency';
    severity: 'low' | 'medium' | 'high' | 'critical';
    description: string;
    affectedComponents: string[];
    probability: number;
    impact: number;
    mitigation: string;
}
export interface Vulnerability {
    id: string;
    type: 'security' | 'performance' | 'maintenance' | 'scalability';
    description: string;
    cveId?: string;
    severity: 'low' | 'medium' | 'high' | 'critical';
    affectedVersions?: string[];
    fixVersion?: string;
    workaround?: string;
}
export interface MitigationStep {
    id: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    action: string;
    estimatedEffort: number;
    dependencies: string[];
    timeline: string;
    owner?: string;
}
export interface DependencyRecommendation {
    id: string;
    type: 'refactor' | 'upgrade' | 'remove' | 'replace' | 'optimize';
    priority: 'low' | 'medium' | 'high' | 'critical';
    title: string;
    description: string;
    benefits: string[];
    risks: string[];
    effort: 'low' | 'medium' | 'high';
    timeline: string;
}
export interface OptimizationSuggestion {
    id: string;
    category: 'performance' | 'maintainability' | 'security' | 'scalability';
    title: string;
    description: string;
    currentState: string;
    proposedState: string;
    expectedBenefit: string;
    implementationComplexity: 'low' | 'medium' | 'high';
    prerequisites: string[];
}
export interface ImpactAnalysisRequest {
    id: string;
    changes: ChangeRequest[];
    analysisDepth: 'immediate' | 'extended' | 'comprehensive';
    includeRiskAssessment: boolean;
    testSuggestions: boolean;
}
export interface ChangeRequest {
    type: 'create' | 'modify' | 'delete' | 'rename';
    target: string;
    description: string;
    estimatedSize: 'small' | 'medium' | 'large';
}
export declare class DependencyAnalyzer extends EventEmitter {
    private options;
    private inferenceEngine;
    private problemDecomposer;
    private activeAnalyses;
    private cache;
    constructor(options?: {
        cacheSize?: number;
        cacheTTL?: number;
        maxConcurrentAnalyses?: number;
        enableRealTimeMonitoring?: boolean;
    });
    /**
     * Analyze project dependencies with comprehensive analysis
     */
    analyzeDependencies(request: DependencyAnalysisRequest): Promise<DependencyAnalysisResult>;
    /**
     * Perform impact analysis for potential changes
     */
    analyzeImpact(request: ImpactAnalysisRequest): Promise<ImpactAnalysis>;
    private validateAnalysisRequest;
    private createAnalysisProblem;
    private createAnalysisQuery;
    private buildDependencyGraph;
    private detectCircularDependencies;
    private calculateDependencyMetrics;
    private assessRisks;
    private determineAnalysisComplexity;
    private generateCacheKey;
    private isCacheValid;
    private cleanupCache;
    private generateNodeId;
    private extractFileName;
    private inferNodeType;
    private estimateComplexity;
    private assessNodeImportance;
    private populateDependents;
    private buildEdges;
    private assessCycleSeverity;
    private generateCycleFixes;
    private findAffectedComponents;
    private calculateMaxDepth;
    private findCriticalPath;
    private calculateModularityScore;
    private calculateCohesionScore;
    private calculateCouplingScore;
    private calculateStabilityIndex;
    private getModuleName;
    private calculateOverallRisk;
    private createMitigationPlan;
    private generateContingencyActions;
    private generateRecommendations;
    private generateOptimizationSuggestions;
    private performImpactAnalysis;
}
