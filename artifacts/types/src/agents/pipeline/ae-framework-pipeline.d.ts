/**
 * AE Framework Pipeline Orchestrator
 * Provides standardized pipeline execution for the 6-phase AE Framework workflow
 */
import { ProcessingContext, PhaseResult, PhaseType, StandardAEAgent, IntentInput, AgentError } from '../interfaces/standard-interfaces.js';
/**
 * Pipeline execution configuration
 */
export interface PipelineConfig {
    projectId: string;
    domain: string;
    enableParallelProcessing?: boolean;
    validateInputs?: boolean;
    retryFailures?: boolean;
    maxRetries?: number;
    timeoutMs?: number;
}
/**
 * Pipeline execution result
 */
export interface PipelineResult {
    success: boolean;
    config: PipelineConfig;
    phases: PhaseResult[];
    totalDuration: number;
    errors: AgentError[];
    metadata: PipelineMetadata;
}
/**
 * Pipeline metadata
 */
export interface PipelineMetadata {
    startTime: Date;
    endTime: Date;
    version: string;
    agentsUsed: string[];
    dataFlowTrace: DataFlowTrace[];
}
/**
 * Data flow tracing for debugging
 */
export interface DataFlowTrace {
    phase: PhaseType;
    inputSize: number;
    outputSize: number;
    transformations: string[];
}
/**
 * AE Framework Pipeline orchestrator class
 */
export declare class AEFrameworkPipeline {
    private agents;
    private config;
    constructor(config: PipelineConfig);
    /**
     * Register an agent for a specific phase
     */
    registerAgent(phase: PhaseType, agent: StandardAEAgent): void;
    /**
     * Execute complete 6-phase AE Framework pipeline
     */
    executePipeline(input: IntentInput): Promise<PipelineResult>;
    /**
     * Execute a single phase with error handling and retries
     */
    executePhase<TInput, TOutput>(phase: PhaseType, input: TInput, context?: ProcessingContext): Promise<PhaseResult<TOutput>>;
    /**
     * Get pipeline status and capabilities
     */
    getPipelineCapabilities(): Record<PhaseType, any>;
    /**
     * Validate pipeline configuration
     */
    validatePipeline(): {
        valid: boolean;
        missing: PhaseType[];
        errors: string[];
    };
    private buildPipelineResult;
    private traceDataFlow;
    private withTimeout;
    private delay;
}
