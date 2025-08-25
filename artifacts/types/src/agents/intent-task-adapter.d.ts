/**
 * Intent Task Adapter for Claude Code
 *
 * This adapter integrates Intent Agent with Claude Code's Task tool,
 * enabling seamless Phase 1 Intent workflow integration and proactive assistance.
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
export declare class IntentTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for Intent-related tasks from Claude Code
     */
    handleIntentTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive Intent suggestions for Claude Code's autonomous operation
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
    private handleRequirementsAnalysis;
    private handleNaturalLanguageExtraction;
    private handleUserStoryCreation;
    private handleCompletenessValidation;
    private handleDomainModeling;
    private handleGenericIntentGuidance;
    private classifyTask;
    private extractRequirementSources;
    private extractProjectContext;
    private extractTextContent;
    private extractRequirementsList;
    private formatIntentAnalysis;
    private formatExtractedRequirements;
    private formatUserStories;
    private formatCompletenessValidation;
    private formatDomainModel;
    private generateIntentRecommendations;
    private identifyIntentWarnings;
    private analyzeRecentActivity;
}
export declare const createIntentTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};
