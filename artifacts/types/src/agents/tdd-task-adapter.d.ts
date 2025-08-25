/**
 * TDD Task Adapter for Claude Code
 *
 * This adapter integrates TDD guidance with Claude Code's Task tool,
 * enabling seamless TDD workflow integration and proactive assistance.
 */
export interface TaskRequest {
    description: string;
    prompt: string;
    subagent_type: string;
}
export interface TaskResponse {
    summary: string;
    analysis: string;
    recommendations: string[];
    nextActions: string[];
    warnings: string[];
    shouldBlockProgress: boolean;
}
export declare class TDDTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for TDD-related tasks from Claude Code
     */
    handleTDDTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive TDD suggestions for Claude Code's autonomous operation
     */
    provideProviacticeGuidance(context: {
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
    private handleFeatureImplementation;
    private handleTDDValidation;
    private handleDevelopmentGuidance;
    private handleComplianceEnforcement;
    private handleCodeAnalysis;
    private handleGenericTDDGuidance;
    private classifyTask;
    private extractFeatureName;
    private extractFilePath;
    private detectCurrentPhase;
    private analyzeRecentActivity;
}
export declare const createTDDTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};
