/**
 * Parallel Strategy for Inference Engine
 * Implements concurrent reasoning with result aggregation
 */
import { ReasoningContext, StrategyResult } from './sequential-strategy.js';
export interface ParallelTask {
    id: string;
    description: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    dependencies: string[];
    input: any;
    estimatedDuration: number;
    maxRetries: number;
}
export interface TaskResult {
    taskId: string;
    success: boolean;
    result: any;
    duration: number;
    confidence: number;
    error?: Error;
}
export interface ParallelExecutionPlan {
    phases: TaskPhase[];
    totalTasks: number;
    estimatedDuration: number;
    resourceRequirements: string[];
}
export interface TaskPhase {
    id: string;
    tasks: ParallelTask[];
    canRunConcurrently: boolean;
    dependencies: string[];
}
export declare class ParallelStrategy {
    private maxConcurrency;
    private activeTaskCount;
    private taskProcessors;
    constructor(options?: {
        maxConcurrency?: number;
    });
    /**
     * Execute parallel reasoning strategy
     */
    execute(context: ReasoningContext): Promise<StrategyResult>;
    /**
     * Register a custom task processor
     */
    registerTaskProcessor(taskType: string, processor: (task: ParallelTask) => Promise<any>): void;
    private registerDefaultProcessors;
    private createExecutionPlan;
    private createTasksFromContext;
    private organizeTasks;
    private executePhase;
    private executeTask;
    private getTaskProcessor;
    private enrichTaskInput;
    private processAnalysisTask;
    private processValidationTask;
    private processComputationTask;
    private processFetchTask;
    private aggregateResults;
    private extractPatterns;
    private calculateStatistics;
    private estimatePhaseTime;
    private identifyResourceRequirements;
    private getPriorityValue;
    private getStepTypeFromTask;
    private calculateTaskConfidence;
    private calculateOverallConfidence;
}
