/**
 * User Stories Task Adapter for Claude Code
 *
 * This adapter integrates Phase 3 (User Stories Creation) processing
 * with Claude Code's Task tool, enabling seamless user story generation,
 * validation, and management workflows.
 */
import { TaskRequest, TaskResponse } from './task-types.js';
export interface UserStory {
    id: string;
    title: string;
    description: string;
    asA: string;
    iWant: string;
    soThat: string;
    acceptanceCriteria: string[];
    priority: 'high' | 'medium' | 'low';
    storyPoints: number;
    epic?: string;
    dependencies: string[];
    testScenarios: string[];
}
export interface UserStorySet {
    stories: UserStory[];
    epics: string[];
    totalStoryPoints: number;
    completenessScore: number;
    gaps: string[];
    conflicts: string[];
}
export declare class UserStoriesTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for User Stories tasks from Claude Code
     */
    handleUserStoriesTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive user story guidance for Claude Code
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
    private handleStoryGeneration;
    private handleStoryValidation;
    private handleStoryPrioritization;
    private handleStoryEstimation;
    private handleAcceptanceCriteriaCreation;
    private handleEpicOrganization;
    private handleDependencyIdentification;
    private handleGenericStoryProcessing;
    private classifyTask;
    private extractRequirementsInput;
    private extractStoriesInput;
    private extractStoryInput;
    generateUserStories(input: string): Promise<UserStorySet>;
    private validateUserStories;
    private prioritizeUserStories;
    private estimateUserStories;
    private createAcceptanceCriteria;
    private organizeStoriesIntoEpics;
    private identifyStoryDependencies;
    private performGenericStoryAnalysis;
    private analyzeRecentActivity;
}
export declare const createUserStoriesTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};
