/**
 * Intent Agent Adapter
 * Adapts the existing IntentAgent to the standardized AE Framework interface
 */
import { StandardAEAgent, ProcessingContext, PhaseResult, ValidationResult, AgentCapabilities, IntentInput, IntentOutput } from '../interfaces/standard-interfaces.js';
/**
 * Adapter that wraps IntentAgent to conform to standard interface
 */
export declare class IntentAgentAdapter implements StandardAEAgent<IntentInput, IntentOutput> {
    private intentAgent;
    readonly agentName = "IntentAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "intent";
    constructor();
    /**
     * Standardized processing method
     */
    process(input: IntentInput, context?: ProcessingContext): Promise<PhaseResult<IntentOutput>>;
    /**
     * Validate input according to standard interface
     */
    validateInput(input: IntentInput): ValidationResult;
    /**
     * Get agent capabilities
     */
    getCapabilities(): AgentCapabilities;
    private extractBusinessModel;
    private extractKeyProcesses;
    private extractSuccessMetrics;
    private extractAssumptions;
    private calculateConfidenceScore;
    private generateWarnings;
    private generateInputHash;
}
