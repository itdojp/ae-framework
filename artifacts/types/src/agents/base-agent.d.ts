/**
 * Base Agent class for all ae-framework agents
 * Provides common functionality for phase state management and steering documents
 */
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { SteeringLoader } from '../utils/steering-loader.js';
import { ValidationResult } from '../cli/types.js';
/**
 * Generic agent output interface for validation
 */
export interface AgentOutput {
    type: 'requirements' | 'specifications' | 'tests' | 'code' | 'verification' | 'deployment' | 'generic';
    content: string;
    artifacts: string[];
    metadata?: Record<string, any>;
    quality?: {
        score: number;
        metrics: Record<string, number>;
    };
}
export declare abstract class BaseAgent {
    protected phaseStateManager: PhaseStateManager;
    protected steeringLoader: SteeringLoader;
    protected phaseName: PhaseType;
    constructor(phaseName: PhaseType);
    /**
     * Initialize phase if not already started
     */
    protected initializePhase(): Promise<void>;
    /**
     * Check if can proceed with current phase
     */
    protected canProceed(): Promise<{
        canProceed: boolean;
        reason?: string;
    }>;
    /**
     * Complete current phase with artifacts
     */
    protected completePhase(artifacts: string[]): Promise<void>;
    /**
     * Get steering context for the agent
     */
    protected getSteeringContext(): Promise<string>;
    /**
     * Get steering documents
     */
    protected getSteeringDocuments(): Promise<Record<string, string>>;
    /**
     * Log phase activity
     */
    protected logActivity(activity: string, metadata?: any): Promise<void>;
    /**
     * Get artifacts from previous phase
     */
    protected getPreviousPhaseArtifacts(): Promise<string[]>;
    /**
     * Check if approvals are required
     */
    protected requiresApproval(): Promise<boolean>;
    /**
     * Generate phase report
     */
    protected generatePhaseReport(): Promise<string>;
    /**
     * Default safe validation method
     * Concrete agents should override this with their specific validation logic
     * Default implementation always passes to prevent system failures
     */
    protected validate(output: AgentOutput): Promise<ValidationResult>;
    /**
     * Wrapper method to ensure validation is always called safely
     * This method should be called by concrete agents after generating output
     */
    protected validateOutput(output: AgentOutput): Promise<ValidationResult>;
    /**
     * Safe logging method that never throws exceptions
     * Falls back to console logging if phase state logging fails
     */
    private safeLogActivity;
}
