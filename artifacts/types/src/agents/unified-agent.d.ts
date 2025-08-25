/**
 * @fileoverview Unified Agent Implementation
 * Phase 2: Agent System Refactoring - Core unified agent architecture
 * Implements domain modeling and TDD as specified in ae-framework-v2.yml
 */
import { AgentTask, TaskResult, AgentConfig, AgentState, AgentContext } from './domain-types.js';
/**
 * Unified Agent class implementing domain model architecture
 * Replaces all individual agent types with a single unified approach
 */
export declare class UnifiedAgent {
    private config;
    private state;
    private phaseStateManager;
    private steeringLoader;
    constructor(config: AgentConfig);
    /**
     * Initialize agent for operation
     */
    initialize(): Promise<void>;
    /**
     * Core task processing method - unified interface for all task types
     */
    processTask(task: AgentTask): Promise<TaskResult>;
    /**
     * Execute task based on type - unified implementation
     */
    private executeTaskByType;
    /**
     * Handle code generation tasks
     */
    private handleCodeGeneration;
    /**
     * Handle test generation tasks
     */
    private handleTestGeneration;
    /**
     * Handle validation tasks
     */
    private handleValidation;
    /**
     * Handle quality assurance tasks
     */
    private handleQualityAssurance;
    /**
     * Handle phase validation tasks
     */
    private handlePhaseValidation;
    /**
     * Handle intent analysis tasks
     */
    private handleIntentAnalysis;
    /**
     * Handle formal specification tasks
     */
    private handleFormalSpecification;
    /**
     * Handle verification tasks
     */
    private handleVerification;
    /**
     * Handle deployment tasks
     */
    private handleDeployment;
    /**
     * Handle generic tasks
     */
    private handleGenericTask;
    /**
     * Validate task result against acceptance criteria
     */
    private validateTaskResult;
    /**
     * Update internal metrics after task completion
     */
    private updateTaskMetrics;
    /**
     * Log activity to phase state manager
     */
    private logActivity;
    getType(): string;
    getCapabilities(): string[];
    getContext(): AgentContext;
    getState(): AgentState;
}
