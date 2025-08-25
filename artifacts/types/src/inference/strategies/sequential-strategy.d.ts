/**
 * Sequential Strategy for Inference Engine
 * Implements step-by-step reasoning with validation
 */
export interface ReasoningStep {
    id: string;
    type: 'analyze' | 'deduce' | 'validate' | 'synthesize';
    description: string;
    input: any;
    output?: any;
    confidence: number;
    metadata: {
        startTime: Date;
        endTime?: Date;
        duration: number;
        resources: string[];
    };
}
export interface ReasoningContext {
    domain: string;
    constraints: any[];
    objectives: string[];
    availableData: Record<string, any>;
    previousSteps: ReasoningStep[];
}
export interface StrategyResult {
    success: boolean;
    steps: ReasoningStep[];
    finalConclusion: any;
    confidence: number;
    reasoning: string[];
}
export declare class SequentialStrategy {
    private stepProcessors;
    constructor();
    /**
     * Execute sequential reasoning strategy
     */
    execute(context: ReasoningContext): Promise<StrategyResult>;
    /**
     * Register a custom step processor
     */
    registerStepProcessor(type: string, processor: (step: ReasoningStep, context: ReasoningContext) => Promise<any>): void;
    private registerDefaultProcessors;
    private createAnalysisStep;
    private createDeductionStep;
    private createValidationStep;
    private createSynthesisStep;
    private processStep;
    private processAnalysisStep;
    private processDeductionStep;
    private processValidationStep;
    private processSynthesisStep;
    private identifyPatterns;
    private isRelevantConstraint;
    private assessDataQuality;
    private generateHypotheses;
    private filterByConstraints;
    private checkConstraint;
    private validateConclusions;
    private extractKeyFindings;
    private generateRecommendations;
    private calculateStepConfidence;
    private calculateOverallConfidence;
}
