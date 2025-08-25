/**
 * Smart Persona Manager for ae-framework
 * Adapts AI behavior based on user patterns and preferences
 */
export interface UserPreferences {
    verbosity: 'minimal' | 'normal' | 'detailed';
    codeStyle: 'functional' | 'object-oriented' | 'mixed';
    explanationLevel: 'beginner' | 'intermediate' | 'expert';
    preferredLanguages: string[];
    preferredFrameworks: string[];
    testingPreference: 'unit' | 'integration' | 'e2e' | 'all';
    suggestionFrequency: 'low' | 'medium' | 'high';
    autoValidation: boolean;
    evidenceRequirement: 'low' | 'medium' | 'high';
}
export interface WorkingContext {
    currentProject: string;
    recentCommands: string[];
    frequentPatterns: string[];
    timeOfDay: 'morning' | 'afternoon' | 'evening' | 'night';
    workSession: {
        startTime: string;
        commandCount: number;
        errorCount: number;
        successRate: number;
    };
}
export interface PersonaProfile {
    id: string;
    name: string;
    description: string;
    preferences: UserPreferences;
    adaptationRules: AdaptationRule[];
    learningData: LearningData;
}
export interface AdaptationRule {
    trigger: {
        context?: Partial<WorkingContext>;
        command?: string;
        pattern?: RegExp;
    };
    adaptation: {
        verbosity?: UserPreferences['verbosity'];
        suggestionBehavior?: 'proactive' | 'reactive' | 'minimal';
        evidenceLevel?: 'strict' | 'normal' | 'relaxed';
    };
    confidence: number;
}
export interface LearningData {
    commandUsage: Record<string, number>;
    successPatterns: string[];
    errorPatterns: string[];
    timePreferences: Record<string, number>;
    lastUpdated: string;
}
export declare class PersonaManager {
    private profilePath;
    private currentProfile;
    private workingContext;
    private interactionCount;
    private saveThreshold;
    constructor(projectRoot: string);
    /**
     * Initialize or load user persona profile
     */
    initialize(): Promise<PersonaProfile>;
    /**
     * Get current persona profile
     */
    getCurrentProfile(): PersonaProfile | null;
    /**
     * Update working context with new command execution
     */
    updateContext(command: string, success: boolean): void;
    /**
     * Learn from user interactions and adapt preferences
     */
    learnFromInteraction(command: string, context: any, feedback?: 'positive' | 'negative'): Promise<void>;
    /**
     * Get adapted behavior based on current context and learned patterns
     */
    getAdaptedBehavior(command: string, context?: any): {
        verbosity: UserPreferences['verbosity'];
        suggestionBehavior: 'proactive' | 'reactive' | 'minimal';
        evidenceLevel: 'strict' | 'normal' | 'relaxed';
        recommendations: string[];
    };
    /**
     * Get personalized command suggestions based on context and history
     */
    getPersonalizedSuggestions(currentCommand?: string): string[];
    /**
     * Update user preferences based on explicit feedback
     */
    updatePreferences(updates: Partial<UserPreferences>): Promise<void>;
    /**
     * Export persona data for backup or migration
     */
    exportPersonaData(): Promise<string>;
    /**
     * Import persona data from backup
     */
    importPersonaData(data: string): Promise<void>;
    private initializeWorkingContext;
    private profileExists;
    private loadProfile;
    private saveProfile;
    private createDefaultProfile;
    private createEmergencyProfile;
    private updateFrequentPatterns;
    private extractPattern;
    private extractCommandPattern;
    private getTimeSlot;
    private matchesRule;
    private getContextValue;
    private compareContextValues;
    private reducedVerbosity;
    private getDefaultBehavior;
    private inferInitialLanguagePreferences;
    /**
     * Update language preferences based on actual command usage patterns
     */
    private updateLanguagePreferencesFromUsage;
    private extractLanguageHints;
}
