/**
 * UI/UX Agent Adapter (Placeholder Implementation)
 * Provides a standardized interface for UI/UX generation phase
 * TODO: Replace with actual UI/UX generation agent when available
 */
import { StandardAEAgent, ProcessingContext, PhaseResult, ValidationResult, AgentCapabilities, UIUXInput, UIUXOutput } from '../interfaces/standard-interfaces.js';
/**
 * Placeholder UI/UX Agent Adapter
 * Generates basic UI/UX artifacts based on domain model and user stories
 */
export declare class UIUXAgentAdapter implements StandardAEAgent<UIUXInput, UIUXOutput> {
    readonly agentName = "UIUXAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "ui-ux-generation";
    process(input: UIUXInput, context?: ProcessingContext): Promise<PhaseResult<UIUXOutput>>;
    validateInput(input: UIUXInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private generateWireframes;
    private generateWireframeComponents;
    private generateUserFlows;
    private groupStoriesByFlow;
    private generateUIComponents;
    private generateDesignSystem;
    private generatePrototypes;
    private mapTypeToInputType;
    private buildErrorResult;
}
