/**
 * Problem Decomposer for Complex Problem Solving Framework
 * Breaks down complex problems into manageable sub-problems
 */
export interface Problem {
    id: string;
    title: string;
    description: string;
    domain: string;
    complexity: 'low' | 'medium' | 'high' | 'critical';
    priority: 'low' | 'medium' | 'high' | 'critical';
    constraints: Constraint[];
    context: Record<string, any>;
    expectedOutcome?: string;
    deadline?: Date;
}
export interface Constraint {
    id: string;
    type: 'resource' | 'time' | 'quality' | 'dependency' | 'business' | 'technical';
    description: string;
    importance: 'low' | 'medium' | 'high' | 'critical';
    value?: any;
    operator?: '>' | '<' | '>=' | '<=' | '=' | '!=' | 'in' | 'not_in';
}
export interface SubProblem {
    id: string;
    parentId: string;
    title: string;
    description: string;
    type: 'sequential' | 'parallel' | 'conditional' | 'loop';
    dependencies: string[];
    estimatedComplexity: number;
    estimatedTime: number;
    requiredResources: string[];
    constraints: Constraint[];
    successCriteria: string[];
    fallbackStrategies: string[];
}
export interface DecompositionResult {
    originalProblem: Problem;
    subProblems: SubProblem[];
    executionPlan: ExecutionNode[];
    estimatedTotalTime: number;
    criticalPath: string[];
    riskAssessment: RiskAssessment;
    recommendations: string[];
}
export interface ExecutionNode {
    id: string;
    subProblemId: string;
    phase: number;
    canRunInParallel: boolean;
    dependencies: string[];
    estimatedStartTime: number;
    estimatedEndTime: number;
}
export interface RiskAssessment {
    overallRisk: 'low' | 'medium' | 'high' | 'critical';
    riskFactors: RiskFactor[];
    mitigationStrategies: MitigationStrategy[];
    contingencyPlan: string[];
}
export interface RiskFactor {
    id: string;
    description: string;
    probability: number;
    impact: number;
    category: 'technical' | 'resource' | 'time' | 'quality' | 'external';
    mitigation?: string;
}
export interface MitigationStrategy {
    riskId: string;
    strategy: string;
    cost: number;
    effectiveness: number;
    timeRequired: number;
}
export declare class ProblemDecomposer {
    private decompositionStrategies;
    private complexityAnalyzers;
    constructor();
    /**
     * Decompose a complex problem into manageable sub-problems
     */
    decompose(problem: Problem): Promise<DecompositionResult>;
    /**
     * Register a custom decomposition strategy
     */
    registerDecompositionStrategy(domain: string, strategy: (problem: Problem) => SubProblem[]): void;
    /**
     * Register a custom complexity analyzer
     */
    registerComplexityAnalyzer(domain: string, analyzer: (problem: Problem) => number): void;
    private registerDefaultStrategies;
    private registerDefaultAnalyzers;
    private validateProblem;
    private analyzeComplexity;
    private selectDecompositionStrategy;
    private generateSubProblems;
    private decomposeSoftwareProblem;
    private decomposeDataProblem;
    private decomposeSystemProblem;
    private decomposeDebuggingProblem;
    private decomposeOptimizationProblem;
    private decomposeGenericProblem;
    private analyzeSoftwareComplexity;
    private analyzeDataComplexity;
    private analyzeGenericComplexity;
    private applyDecompositionStrategy;
    private applyHierarchicalStrategy;
    private applyModularStrategy;
    private applySequentialStrategy;
    private optimizeSubProblems;
    private removeRedundantDependencies;
    private balanceWorkload;
    private createExecutionPlan;
    private calculateTotalTime;
    private findCriticalPath;
    private performRiskAssessment;
    private findLongDependencyChains;
    private calculateOverallRisk;
    private generateMitigationStrategies;
    private createContingencyPlan;
    private generateRecommendations;
}
