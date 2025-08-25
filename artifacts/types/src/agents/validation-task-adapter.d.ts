/**
 * Validation Task Adapter for Claude Code
 *
 * This adapter integrates Phase 4 (Validation) processing with Claude Code's
 * Task tool, enabling seamless validation workflows for requirements,
 * user stories, specifications, and code quality.
 */
import { TaskRequest, TaskResponse } from './task-types.js';
export interface ValidationResult {
    isValid: boolean;
    score: number;
    issues: ValidationIssue[];
    recommendations: string[];
    coverageReport: CoverageReport;
}
export interface ValidationIssue {
    id: string;
    type: 'error' | 'warning' | 'info';
    severity: 'critical' | 'high' | 'medium' | 'low';
    category: string;
    description: string;
    location?: string;
    suggestion?: string;
}
export interface CoverageReport {
    functional: number;
    nonFunctional: number;
    business: number;
    technical: number;
    overall: number;
}
export declare class ValidationTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for Validation tasks from Claude Code
     */
    handleValidationTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive validation guidance for Claude Code
     */
    provideProactiveGuidance(context: {
        recentFiles: string[];
        recentActions: string[];
        userIntent: string;
    }): Promise<{
        shouldIntervene: boolean;
        intervention: {
            type: 'warning' | 'suggestion' | 'block';
            message: string;
            recommendedActions: string[];
        };
    }>;
    private handleRequirementsValidation;
    private handleUserStoriesValidation;
    private handleSpecificationValidation;
    private handleTraceabilityValidation;
    private handleCompletenessValidation;
    private handleConsistencyValidation;
    private handleFeasibilityValidation;
    private handleCrossValidation;
    private handleGenericValidation;
    private classifyTask;
    private extractRequirementsInput;
    private extractStoriesInput;
    private extractSpecificationInput;
    private extractTraceabilityInput;
    private extractCompletenessInput;
    private extractConsistencyInput;
    private extractFeasibilityInput;
    private extractCrossValidationInput;
    private extractGenericInput;
    private validateRequirements;
    validateUserStories(input: any): Promise<any>;
    private validateSpecifications;
    private validateTraceability;
    private validateCompleteness;
    private validateConsistency;
    private validateFeasibility;
    private performCrossValidation;
    private performGenericValidation;
    private analyzeRecentActivity;
}
export declare const createValidationTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};
