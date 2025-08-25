/**
 * Sequential Inference Engine for ae-framework
 * Provides multi-step reasoning with validation and rollback capabilities
 */
import { EventEmitter } from 'events';
export interface ComplexQuery {
    id: string;
    description: string;
    context: Record<string, any>;
    constraints: Constraint[];
    expectedOutcome?: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
}
export interface Constraint {
    type: 'logical' | 'temporal' | 'resource' | 'dependency';
    condition: string;
    severity: 'warning' | 'error' | 'critical';
}
export interface InferenceStep {
    id: string;
    description: string;
    input: Record<string, any>;
    output?: Record<string, any>;
    confidence: number;
    duration: number;
    dependencies: string[];
    status: 'pending' | 'running' | 'completed' | 'failed' | 'skipped';
    error?: Error;
}
export interface InferenceResult {
    queryId: string;
    success: boolean;
    confidence: number;
    totalSteps: number;
    completedSteps: number;
    steps: InferenceStep[];
    finalResult?: any;
    error?: Error;
    metadata: {
        startTime: Date;
        endTime?: Date;
        duration: number;
        memoryUsed: number;
        cacheHits: number;
    };
}
export interface ProjectContext {
    projectRoot: string;
    packageJson?: any;
    tsConfig?: any;
    sourceFiles: string[];
    dependencies: Record<string, string>;
    devDependencies: Record<string, string>;
    buildConfig?: any;
}
export interface DependencyNode {
    id: string;
    type: 'file' | 'module' | 'function' | 'class';
    path: string;
    dependencies: string[];
    dependents: string[];
    weight: number;
    metadata: Record<string, any>;
}
export interface DependencyGraph {
    nodes: DependencyNode[];
    edges: Array<{
        from: string;
        to: string;
        type: string;
        weight: number;
    }>;
    cycles: string[][];
    criticalPaths: string[][];
    metrics: {
        totalNodes: number;
        totalEdges: number;
        cycleCount: number;
        maxDepth: number;
        fanOut: Record<string, number>;
    };
}
export interface ChangeSet {
    id: string;
    description: string;
    files: FileChange[];
    timestamp: Date;
    author: string;
}
export interface FileChange {
    path: string;
    type: 'create' | 'modify' | 'delete' | 'rename';
    oldPath?: string;
    content?: string;
    lines?: {
        added: number;
        removed: number;
        modified: number;
    };
}
export interface ImpactAnalysis {
    changeSetId: string;
    affectedComponents: AffectedComponent[];
    riskLevel: 'low' | 'medium' | 'high' | 'critical';
    estimatedEffort: number;
    recommendations: string[];
    testingRequirements: TestRequirement[];
    rollbackPlan?: string[];
}
export interface AffectedComponent {
    id: string;
    path: string;
    type: 'direct' | 'indirect' | 'cascade';
    impactLevel: 'minimal' | 'moderate' | 'significant' | 'critical';
    description: string;
    dependencies: string[];
}
export interface TestRequirement {
    type: 'unit' | 'integration' | 'e2e' | 'performance';
    priority: 'low' | 'medium' | 'high' | 'critical';
    description: string;
    estimatedTime: number;
}
export declare class SequentialInferenceEngine extends EventEmitter {
    private options;
    private cache;
    private activeQueries;
    private stepHandlers;
    constructor(options?: {
        maxConcurrentQueries?: number;
        cacheSize?: number;
        timeoutMs?: number;
        enableProfiling?: boolean;
    });
    /**
     * Process a complex query using sequential reasoning
     */
    processComplexQuery(query: ComplexQuery): Promise<InferenceResult>;
    /**
     * Analyze deep dependencies in a project context
     */
    analyzeDeepDependencies(context: ProjectContext): Promise<DependencyGraph>;
    /**
     * Evaluate the impact scope of changes
     */
    evaluateImpactScope(changes: ChangeSet): Promise<ImpactAnalysis>;
    private registerDefaultHandlers;
    private decomposeQuery;
    private checkStepDependencies;
    private executeStep;
    private validateStepResult;
    private shouldAbortOnStepFailure;
    private synthesizeResult;
    private handleAnalyzeStep;
    private handleValidateStep;
    private handleSynthesizeStep;
    private analyzeFileDependencies;
    private detectCycles;
    private findCriticalPaths;
    private calculateMaxDepth;
    private calculateFanOut;
    private analyzeDirectImpacts;
    private analyzeIndirectImpacts;
    private calculateRiskLevel;
    private estimateEffort;
    private generateRecommendations;
    private defineTestingRequirements;
    private createRollbackPlan;
    private getMemoryUsage;
}
