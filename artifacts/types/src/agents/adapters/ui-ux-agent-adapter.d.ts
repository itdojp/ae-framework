/**
 * UI/UX Agent Adapter
 * Standardized UI/UX generation phase backed by UIUXTaskAdapter.
 */
import type { AgentCapabilities, PhaseResult, ProcessingContext, StandardAEAgent, UIUXInput, UIUXOutput, ValidationResult } from '../interfaces/standard-interfaces.js';
export declare class UIUXAgentAdapter implements StandardAEAgent<UIUXInput, UIUXOutput> {
    readonly agentName = "UIUXAgentAdapter";
    readonly version = "1.1.0";
    readonly supportedPhase: "ui-ux-generation";
    private uiuxTaskAdapter;
    constructor();
    process(input: UIUXInput, context?: ProcessingContext): Promise<PhaseResult<UIUXOutput>>;
    validateInput(input: UIUXInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildErrorResult;
}
