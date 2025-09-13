/**
 * Persona Integration Service for ae-framework
 * Integrates Smart Persona System with existing commands
 */

import { PersonaManager } from '../utils/persona-manager.js';
import type { UserPreferences } from '../utils/persona-manager.js';
import type { CommandResult, CommandContext } from '../commands/slash-command-manager.js';

export interface AdaptedCommandBehavior {
  verbosity: UserPreferences['verbosity'];
  includeExplanations: boolean;
  suggestionLevel: 'minimal' | 'moderate' | 'comprehensive';
  evidenceValidation: boolean;
  proactiveSuggestions: string[];
}

export class PersonaIntegrationService {
  private personaManager: PersonaManager;
  private initialized: boolean = false;

  constructor(projectRoot: string) {
    this.personaManager = new PersonaManager(projectRoot);
  }

  /**
   * Initialize the persona integration service
   */
  async initialize(): Promise<void> {
    if (!this.initialized) {
      await this.personaManager.initialize();
      this.initialized = true;
    }
  }

  /**
   * Adapt command behavior based on persona preferences
   */
  async adaptCommandBehavior(command: string, context?: any): Promise<AdaptedCommandBehavior> {
    if (!this.initialized) {
      await this.initialize();
    }

    const behavior = this.personaManager.getAdaptedBehavior(command, context);
    const suggestions = this.personaManager.getPersonalizedSuggestions(command);

    return {
      verbosity: behavior.verbosity,
      includeExplanations: behavior.verbosity !== 'minimal',
      suggestionLevel: this.mapSuggestionBehavior(behavior.suggestionBehavior),
      evidenceValidation: behavior.evidenceLevel === 'strict',
      proactiveSuggestions: behavior.suggestionBehavior === 'proactive' ? suggestions : []
    };
  }

  /**
   * Learn from command execution results
   */
  async learnFromExecution(
    command: string,
    result: CommandResult,
    context?: any,
    userFeedback?: 'positive' | 'negative'
  ): Promise<void> {
    if (!this.initialized) return;

    // Update working context
    this.personaManager.updateContext(command, result.success);

    // Learn from interaction
    await this.personaManager.learnFromInteraction(command, context, userFeedback);
  }

  /**
   * Apply persona adaptations to command result
   */
  async adaptCommandResult(
    result: CommandResult,
    command: string,
    adaptedBehavior: AdaptedCommandBehavior
  ): Promise<CommandResult> {
    const adaptedResult = { ...result };

    // Adjust verbosity of the response
    if (adaptedBehavior.verbosity === 'minimal') {
      adaptedResult.message = this.minimizeMessage(result.message);
    } else if (adaptedBehavior.verbosity === 'detailed') {
      adaptedResult.message = await this.enhanceMessage(result.message, command, result);
    }

    // Add proactive suggestions if enabled
    if (adaptedBehavior.proactiveSuggestions.length > 0) {
      adaptedResult.data = {
        ...result.data,
        personaSuggestions: adaptedBehavior.proactiveSuggestions
      };
    }

    return adaptedResult;
  }

  /**
   * Get persona-aware validation options
   */
  getValidationOptions(command: string): { validate: boolean; minConfidence: number } {
    if (!this.initialized) {
      return { validate: false, minConfidence: 0.7 };
    }

    const behavior = this.personaManager.getAdaptedBehavior(command);
    
    let minConfidence = 0.7;
    switch (behavior.evidenceLevel) {
      case 'strict': minConfidence = 0.9; break;
      case 'normal': minConfidence = 0.7; break;
      case 'relaxed': minConfidence = 0.5; break;
    }

    const profile = this.personaManager.getCurrentProfile();
    const shouldValidate = profile?.preferences['autoValidation'] || behavior.evidenceLevel === 'strict';

    return { validate: shouldValidate, minConfidence };
  }

  /**
   * Get persona-specific command options
   */
  getPersonalizedCommandOptions(command: string): Record<string, any> {
    if (!this.initialized) return {};

    const profile = this.personaManager.getCurrentProfile();
    if (!profile) return {};

    const options: Record<string, any> = {};

    // Add language preferences for analysis commands
    if (command.includes('analyze') || command.includes('improve')) {
      if (profile.preferences['preferredLanguages'].length > 0) {
        options['languages'] = profile.preferences['preferredLanguages'];
      }
    }

    // Add testing preferences for code generation
    if (command.includes('generate') || command.includes('create')) {
      options['testingStyle'] = profile.preferences['testingPreference'];
      options['codeStyle'] = profile.preferences['codeStyle'];
    }

    // Add documentation level preferences
    if (command.includes('document')) {
      options['explanationLevel'] = profile.preferences['explanationLevel'];
    }

    return options;
  }

  /**
   * Provide contextual help based on user patterns
   */
  getContextualHelp(command: string, error?: string): string[] {
    if (!this.initialized) return [];

    const profile = this.personaManager.getCurrentProfile();
    if (!profile) return [];

    const help: string[] = [];

    // Check for common error patterns
    if (error) {
      for (const errorPattern of profile.learningData.errorPatterns) {
        if (errorPattern.includes(command)) {
          help.push(`Based on previous patterns, try: ${errorPattern.split(':')[0]}`);
        }
      }
    }

    // Suggest based on success patterns
    for (const successPattern of profile.learningData.successPatterns) {
      if (successPattern.includes(command) && Math.random() < 0.3) {
        help.push(`Previously successful: ${successPattern.split(':')[0]}`);
      }
    }

    return help.slice(0, 2); // Limit to 2 suggestions
  }

  /**
   * Update user preferences from command usage patterns
   */
  async updatePreferencesFromUsage(): Promise<void> {
    if (!this.initialized) return;

    const profile = this.personaManager.getCurrentProfile();
    if (!profile) return;

    const commandUsage = profile.learningData.commandUsage;
    const updates: Partial<UserPreferences> = {};

    // Analyze most used commands to infer preferences
    const mostUsedCommand = Object.entries(commandUsage)
      .sort(([,a], [,b]) => b - a)[0];

    if (mostUsedCommand) {
      const [command] = mostUsedCommand;
      
      // Infer preferred languages from analyze commands
      if (command.includes('analyze')) {
        // This would need more sophisticated analysis in practice
        updates.preferredLanguages = ['typescript', 'javascript'];
      }

      // Infer testing preference from frequent test-related commands
      if (command.includes('test')) {
        updates.testingPreference = 'all';
      }
    }

    // Update if we have inferred preferences
    if (Object.keys(updates).length > 0) {
      await this.personaManager.updatePreferences(updates);
    }
  }

  /**
   * Get persona manager instance for direct access
   */
  getPersonaManager(): PersonaManager {
    return this.personaManager;
  }

  // Private helper methods

  private mapSuggestionBehavior(behavior: 'proactive' | 'reactive' | 'minimal'): 'minimal' | 'moderate' | 'comprehensive' {
    switch (behavior) {
      case 'proactive': return 'comprehensive';
      case 'reactive': return 'moderate';
      case 'minimal': return 'minimal';
    }
  }

  private minimizeMessage(message: string | undefined): string {
    if (!message) return '';
    
    // Extract the key information, remove explanatory text
    const lines = message.split('\n');
    const keyLine = lines.find(line => 
      line.includes('Found') || 
      line.includes('Generated') || 
      line.includes('Analyzed') ||
      line.includes('Success') ||
      line.includes('Error')
    );
    
    return keyLine || lines[0] || message;
  }

  private async enhanceMessage(message: string | undefined, command: string, result: CommandResult): Promise<string> {
    if (!message) return '';

    let enhanced = message;

    // Add context based on command type
    if (command.includes('analyze')) {
      enhanced += '\n\nℹ️ Tip: Use --security flag for security analysis, --performance for performance checks';
    } else if (command.includes('troubleshoot')) {
      enhanced += '\n\nℹ️ Tip: Use --logs=path to analyze specific log files';
    } else if (command.includes('improve')) {
      enhanced += '\n\nℹ️ Tip: Use --apply to automatically apply safe improvements';
    }

    // Add success/failure context
    if (result.success && result.data) {
      enhanced += '\n\n✨ Command completed successfully with data available';
    } else if (!result.success) {
      enhanced += '\n\n⚠️ Command failed - consider using /ae:troubleshoot for help';
    }

    return enhanced;
  }
}
