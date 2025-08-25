/**
 * Natural Language Requirements Task Adapter for Claude Code
 *
 * This adapter integrates Phase 2 (Natural Language Requirements) processing
 * with Claude Code's Task tool, enabling seamless requirements analysis and
 * natural language processing workflows.
 */
import { TaskRequest, TaskResponse, ProactiveGuidanceContext, ProactiveGuidanceResult } from './task-types.js';
export interface RequirementDocument {
    title: string;
    content: string;
    source: string;
    type: 'functional' | 'non-functional' | 'business' | 'technical';
    priority: 'high' | 'medium' | 'low';
    stakeholder?: string;
}
export interface ProcessedRequirements {
    structured: RequirementDocument[];
    summary: string;
    gaps: string[];
    conflicts: string[];
    ambiguities: string[];
    clarificationNeeded: string[];
    processedRequirements?: string;
    naturalLanguageRequirements?: string;
}
export declare class NaturalLanguageTaskAdapter {
    private agent;
    private static readonly MAX_REQUIREMENTS_BEFORE_CONFLICTS;
    constructor();
    /**
     * Main handler for Natural Language Requirements tasks from Claude Code
     */
    handleNaturalLanguageTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive natural language processing guidance for Claude Code
     */
    provideProactiveGuidance(context: ProactiveGuidanceContext): Promise<ProactiveGuidanceResult>;
    private handleRequirementsAnalysis;
    private handleEntityExtraction;
    private handleCompletenessValidation;
    private handleAmbiguityResolution;
    private handleRequirementsStructuring;
    private handleGapIdentification;
    private handleGenericNLProcessing;
    private classifyTask;
    private extractRequirementsText;
    processNaturalLanguageRequirements(text: string): Promise<ProcessedRequirements>;
    private inferRequirementType;
    private inferPriority;
    private identifyStructuralGaps;
    private detectConflicts;
    private detectAmbiguousLanguage;
    private generateClarificationQuestions;
    private extractBusinessEntities;
    private validateRequirementsCompleteness;
    private identifyAmbiguities;
    private structureRequirements;
    private identifyRequirementGaps;
    private performGenericNLAnalysis;
    private analyzeRecentActivity;
}
export declare const createNaturalLanguageTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: ProactiveGuidanceContext) => Promise<ProactiveGuidanceResult>;
};
