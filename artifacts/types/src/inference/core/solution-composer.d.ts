/**
 * Solution Composer for Complex Problem Solving Framework
 * Integrates and validates solutions from sub-problems
 */
import type { DecompositionResult } from './problem-decomposer.js';
export interface SubSolution {
    subProblemId: string;
    success: boolean;
    confidence: number;
    result: any;
    metrics: {
        executionTime: number;
        resourcesUsed: string[];
        qualityScore: number;
    };
    validationResults: ValidationResult[];
    dependencies: Record<string, any>;
    error?: Error;
}
export interface ValidationResult {
    criterion: string;
    passed: boolean;
    score: number;
    details: string;
    importance: 'low' | 'medium' | 'high' | 'critical';
}
export interface CompositeSolution {
    problemId: string;
    success: boolean;
    overallConfidence: number;
    compositeResult: any;
    subSolutions: SubSolution[];
    integrationMetrics: {
        consistencyScore: number;
        completenessScore: number;
        qualityScore: number;
        performanceScore: number;
    };
    validationResults: GlobalValidationResult[];
    recommendations: string[];
    alternatives?: AlternativeSolution[];
}
export interface GlobalValidationResult {
    aspect: 'consistency' | 'completeness' | 'quality' | 'performance' | 'security';
    passed: boolean;
    score: number;
    details: string;
    requiredActions: string[];
}
export interface AlternativeSolution {
    id: string;
    description: string;
    confidence: number;
    tradeoffs: string[];
    estimatedImpact: {
        time: number;
        resources: number;
        quality: number;
    };
}
export interface CompositionStrategy {
    name: string;
    description: string;
    canHandle: (decomposition: DecompositionResult) => boolean;
    compose: (subSolutions: SubSolution[], context: CompositionContext) => Promise<any>;
    validate: (result: any, context: CompositionContext) => Promise<ValidationResult[]>;
}
export interface CompositionContext {
    originalProblem: any;
    decompositionResult: DecompositionResult;
    constraints: any[];
    qualityThresholds: Record<string, number>;
    integrationRules: IntegrationRule[];
}
export interface IntegrationRule {
    id: string;
    type: 'dependency' | 'consistency' | 'transformation' | 'validation';
    description: string;
    condition: (subSolutions: SubSolution[]) => boolean;
    action: (subSolutions: SubSolution[]) => SubSolution[] | void;
    priority: 'low' | 'medium' | 'high' | 'critical';
}
export declare class SolutionComposer {
    private strategies;
    private validators;
    private transformers;
    constructor();
    /**
     * Compose solutions from sub-problems into a complete solution
     */
    compose(subSolutions: SubSolution[], decompositionResult: DecompositionResult, context?: Partial<CompositionContext>): Promise<CompositeSolution>;
    /**
     * Register a custom composition strategy
     */
    registerCompositionStrategy(strategy: CompositionStrategy): void;
    /**
     * Register a custom validator
     */
    registerValidator(name: string, validator: (result: any, context: CompositionContext) => Promise<ValidationResult[]>): void;
    private registerDefaultStrategies;
    private registerDefaultValidators;
    private registerDefaultTransformers;
    private validateInputSolutions;
    private preprocessSolutions;
    private selectCompositionStrategy;
    private composeSequential;
    private composeParallel;
    private composeHierarchical;
    private composeHybrid;
    private performGlobalValidation;
    private calculateIntegrationMetrics;
    private determineOverallSuccess;
    private calculateOverallConfidence;
    private createDefaultIntegrationRules;
    private resolveDependencies;
    private resolveSubSolutionDependencies;
    private enforceConsistency;
    private normalizeQuality;
    private validateSequential;
    private validateParallel;
    private validateHierarchical;
    private validateHybrid;
    private validateConsistency;
    private validateCompleteness;
    private validateQuality;
    private validatePerformance;
    private validateSecurity;
    private sortByExecutionOrder;
    private groupByExecutionPhase;
    private buildHierarchy;
    private composeHierarchyRecursive;
    private calculateHierarchyLevels;
    private isSequentialSolution;
    private isParallelSolution;
    private integrateHybridResults;
    private hasHierarchicalStructure;
    private applyIntegrationRules;
    private getPriorityValue;
    private generateRecommendations;
    private generateAlternatives;
}
