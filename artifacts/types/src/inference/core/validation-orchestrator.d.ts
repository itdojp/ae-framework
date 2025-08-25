/**
 * Validation Orchestrator for Complex Problem Solving Framework
 * Coordinates validation processes across different solution components
 */
import { EventEmitter } from 'events';
import type { SubSolution, CompositeSolution, ValidationResult } from './solution-composer.js';
export interface ValidationPlan {
    id: string;
    description: string;
    phases: ValidationPhase[];
    totalValidators: number;
    estimatedDuration: number;
    requiredResources: string[];
    criticalityLevel: 'low' | 'medium' | 'high' | 'critical';
}
export interface ValidationPhase {
    id: string;
    name: string;
    description: string;
    validators: ValidatorConfig[];
    dependencies: string[];
    parallel: boolean;
    timeout: number;
    retryPolicy: RetryPolicy;
}
export interface ValidatorConfig {
    id: string;
    type: ValidationCategory;
    name: string;
    description: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    timeout: number;
    retries: number;
    parameters: Record<string, any>;
    successCriteria: SuccessCriteria;
}
export type ValidationCategory = 'structural' | 'functional' | 'performance' | 'security' | 'consistency' | 'completeness' | 'integration' | 'business_rules' | 'data_quality';
export interface SuccessCriteria {
    minScore: number;
    mustPass: boolean;
    allowableFailures?: number;
    customCondition?: (result: ValidationResult) => boolean;
}
export interface RetryPolicy {
    maxRetries: number;
    backoffStrategy: 'linear' | 'exponential' | 'fixed';
    baseDelayMs: number;
    maxDelayMs: number;
}
export interface ValidationExecution {
    planId: string;
    executionId: string;
    startTime: Date;
    endTime?: Date;
    status: 'pending' | 'running' | 'completed' | 'failed' | 'cancelled';
    currentPhase?: string;
    results: ValidationPhaseResult[];
    overallResult: OverallValidationResult;
    metrics: ValidationMetrics;
}
export interface ValidationPhaseResult {
    phaseId: string;
    success: boolean;
    startTime: Date;
    endTime: Date;
    duration: number;
    validatorResults: ValidatorExecutionResult[];
    phaseScore: number;
    criticalFailures: string[];
}
export interface ValidatorExecutionResult {
    validatorId: string;
    success: boolean;
    score: number;
    result: ValidationResult;
    executionTime: number;
    attempts: number;
    error?: Error;
}
export interface OverallValidationResult {
    success: boolean;
    overallScore: number;
    criticalityLevel: 'low' | 'medium' | 'high' | 'critical';
    summary: string;
    passedValidations: number;
    failedValidations: number;
    totalValidations: number;
    recommendations: string[];
    blockers: string[];
}
export interface ValidationMetrics {
    totalDuration: number;
    avgValidatorTime: number;
    successRate: number;
    retryCount: number;
    resourceUtilization: Record<string, number>;
    performanceScore: number;
}
export interface Validator {
    id: string;
    category: ValidationCategory;
    validate: (target: any, context: ValidationContext, config: ValidatorConfig) => Promise<ValidationResult>;
    canHandle: (target: any, context: ValidationContext) => boolean;
}
export interface ValidationContext {
    originalProblem?: any;
    subSolutions?: SubSolution[];
    compositeSolution?: CompositeSolution;
    constraints: any[];
    metadata: Record<string, any>;
}
export declare class ValidationOrchestrator extends EventEmitter {
    private options;
    private validators;
    private activeExecutions;
    private validationPlans;
    constructor(options?: {
        maxConcurrentValidations?: number;
        defaultTimeout?: number;
        enableMetrics?: boolean;
    });
    /**
     * Create a validation plan for a given context
     */
    createValidationPlan(target: any, context: ValidationContext, requirements?: {
        categories?: ValidationCategory[];
        criticalityLevel?: 'low' | 'medium' | 'high' | 'critical';
        maxDuration?: number;
    }): Promise<ValidationPlan>;
    /**
     * Execute a validation plan
     */
    executeValidationPlan(planId: string, target: any, context: ValidationContext): Promise<ValidationExecution>;
    /**
     * Register a custom validator
     */
    registerValidator(validator: Validator): void;
    /**
     * Get validation execution by ID
     */
    getExecution(executionId: string): ValidationExecution | undefined;
    /**
     * Cancel a running validation execution
     */
    cancelExecution(executionId: string): Promise<boolean>;
    private registerDefaultValidators;
    private selectValidators;
    private organizeValidatorsIntoPhases;
    private executeValidationPhase;
    private executeValidator;
    private executeWithTimeout;
    private evaluateValidationResult;
    private calculateRetryDelay;
    private validateStructureCompleteness;
    private validateStructureConsistency;
    private validateFunctionalCorrectness;
    private validatePerformanceMetrics;
    private validateSecurityCompliance;
    private validateDataQuality;
    private validateIntegrationCompatibility;
    private assessDataQuality;
    private hasDataContent;
    private getTargetDescription;
    private getValidatorName;
    private getValidatorDescription;
    private getValidatorPriority;
    private getPriorityValue;
    private estimateValidationDuration;
    private identifyRequiredResources;
    private createEmptyOverallResult;
    private createEmptyMetrics;
    private calculateOverallResult;
    private calculateMetrics;
    private generateValidationRecommendations;
}
