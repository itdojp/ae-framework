/**
 * Task Agent Adapters
 * Adapts existing task adapters to standardized AE Framework interface
 */
import { StandardAEAgent, ProcessingContext, PhaseResult, ValidationResult, AgentCapabilities, RequirementsInput, RequirementsOutput, UserStoriesInput, UserStoriesOutput, ValidationInput, ValidationOutput, DomainModelingInput, DomainModelingOutput } from '../interfaces/standard-interfaces.js';
/**
 * Natural Language Requirements Adapter
 */
export declare class RequirementsAgentAdapter implements StandardAEAgent<RequirementsInput, RequirementsOutput> {
    private nlpAgent;
    readonly agentName = "RequirementsAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "requirements";
    constructor();
    process(input: RequirementsInput, context?: ProcessingContext): Promise<PhaseResult<RequirementsOutput>>;
    validateInput(input: RequirementsInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildNaturalLanguageInput;
    private extractStructuredRequirements;
    private categorizeRequirement;
    private calculateConfidence;
    private generateWarnings;
    private buildErrorResult;
}
/**
 * User Stories Agent Adapter
 */
export declare class UserStoriesAgentAdapter implements StandardAEAgent<UserStoriesInput, UserStoriesOutput> {
    private storiesAgent;
    readonly agentName = "UserStoriesAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "user-stories";
    constructor();
    process(input: UserStoriesInput, context?: ProcessingContext): Promise<PhaseResult<UserStoriesOutput>>;
    validateInput(input: UserStoriesInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildStoriesInput;
    private transformStories;
    private extractAcceptanceCriteria;
    private generateTestScenarios;
    private buildTraceabilityMatrix;
    private buildErrorResult;
}
/**
 * Validation Agent Adapter
 */
export declare class ValidationAgentAdapter implements StandardAEAgent<ValidationInput, ValidationOutput> {
    private validationAgent;
    readonly agentName = "ValidationAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "validation";
    constructor();
    process(input: ValidationInput, context?: ProcessingContext): Promise<PhaseResult<ValidationOutput>>;
    validateInput(input: ValidationInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildValidationReport;
    private calculateQualityScore;
    private buildErrorResult;
}
/**
 * Domain Modeling Agent Adapter
 */
export declare class DomainModelingAgentAdapter implements StandardAEAgent<DomainModelingInput, DomainModelingOutput> {
    private domainAgent;
    readonly agentName = "DomainModelingAgentAdapter";
    readonly version = "1.0.0";
    readonly supportedPhase: "domain-modeling";
    constructor();
    process(input: DomainModelingInput, context?: ProcessingContext): Promise<PhaseResult<DomainModelingOutput>>;
    validateInput(input: DomainModelingInput): ValidationResult;
    getCapabilities(): AgentCapabilities;
    private buildDomainPrompt;
    private transformDomainResult;
    private buildErrorResult;
}
