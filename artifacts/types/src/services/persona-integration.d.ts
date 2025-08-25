/**
 * Persona Integration Service for ae-framework
 * Integrates Smart Persona System with existing commands
 */
import { PersonaManager, UserPreferences } from '../utils/persona-manager.js';
import type { CommandResult } from '../commands/slash-command-manager.js';
export interface AdaptedCommandBehavior {
    verbosity: UserPreferences['verbosity'];
    includeExplanations: boolean;
    suggestionLevel: 'minimal' | 'moderate' | 'comprehensive';
    evidenceValidation: boolean;
    proactiveSuggestions: string[];
}
export declare class PersonaIntegrationService {
    private personaManager;
    private initialized;
    constructor(projectRoot: string);
    /**
     * Initialize the persona integration service
     */
    initialize(): Promise<void>;
    /**
     * Adapt command behavior based on persona preferences
     */
    adaptCommandBehavior(command: string, context?: any): Promise<AdaptedCommandBehavior>;
    /**
     * Learn from command execution results
     */
    learnFromExecution(command: string, result: CommandResult, context?: any, userFeedback?: 'positive' | 'negative'): Promise<void>;
    /**
     * Apply persona adaptations to command result
     */
    adaptCommandResult(result: CommandResult, command: string, adaptedBehavior: AdaptedCommandBehavior): Promise<CommandResult>;
    /**
     * Get persona-aware validation options
     */
    getValidationOptions(command: string): {
        validate: boolean;
        minConfidence: number;
    };
    /**
     * Get persona-specific command options
     */
    getPersonalizedCommandOptions(command: string): Record<string, any>;
    /**
     * Provide contextual help based on user patterns
     */
    getContextualHelp(command: string, error?: string): string[];
    /**
     * Update user preferences from command usage patterns
     */
    updatePreferencesFromUsage(): Promise<void>;
    /**
     * Get persona manager instance for direct access
     */
    getPersonaManager(): PersonaManager;
    private mapSuggestionBehavior;
    private minimizeMessage;
    private enhanceMessage;
}
