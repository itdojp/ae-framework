/**
 * Persona Command for ae-framework
 * Manages Smart Persona System for adaptive AI behavior
 */

import { BaseExtendedCommand } from './base-command.js';
import type { ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { PersonaManager } from '../../utils/persona-manager.js';
import type { UserPreferences, PersonaProfile } from '../../utils/persona-manager.js';

interface PersonaCommandResult {
  action: 'view' | 'update' | 'export' | 'import' | 'reset';
  profile?: PersonaProfile;
  preferences?: UserPreferences;
  message: string;
  data?: any;
}

export class PersonaCommand extends BaseExtendedCommand {
  private personaManager: PersonaManager;

  constructor() {
    super({
      name: '/ae:persona',
      description: 'Manage Smart Persona System settings and preferences',
      usage: '/ae:persona [view|update|export|import|reset] [options]',
      aliases: ['/persona', '/a:persona'],
      category: 'utility'
    });
    
    this.personaManager = new PersonaManager(process.cwd());
  }

  protected override validateArgs(args: string[]): { isValid: boolean; message?: string } {
    if (args.length === 0) {
      // Default to 'view' action
      return { isValid: true };
    }

    const action = args[0];
    const validActions = ['view', 'update', 'export', 'import', 'reset'];
    
    if (!action || !validActions.includes(action)) {
      return {
        isValid: false,
        message: `Invalid action: ${action}. Valid actions: ${validActions.join(', ')}`
      };
    }

    return { isValid: true };
  }

  protected override parseOptions(args: string[]): Record<string, any> {
    const baseOptions = super.parseOptions(args);
    const action = args[0] || 'view';
    
    return {
      ...baseOptions,
      action,
      // Parse key-value pairs for update action
      updates: this.parseUpdateOptions(args.slice(1))
    };
  }

  protected override async execute(
    args: string[], 
    options: any, 
    context: CommandContext
  ): Promise<ExtendedCommandResult<PersonaCommandResult>> {
    try {
      // Initialize persona manager
      await this.personaManager.initialize();

      let result: PersonaCommandResult;

      switch (options.action) {
        case 'view':
          result = await this.handleView();
          break;
        case 'update':
          result = await this.handleUpdate(options.updates);
          break;
        case 'export':
          result = await this.handleExport(options.output);
          break;
        case 'import':
          if (!args[1]) throw new Error('File path is required for import command');
          result = await this.handleImport(args[1]);
          break;
        case 'reset':
          result = await this.handleReset();
          break;
        default:
          result = await this.handleView();
      }

      return {
        success: true,
        message: result.message,
        data: result,
        metrics: {
          executionTime: 0,
          filesProcessed: 1,
          confidence: 1.0
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Persona command failed: ${error.message}`,
        metrics: {
          executionTime: 0,
          filesProcessed: 0
        }
      };
    }
  }

  private async handleView(): Promise<PersonaCommandResult> {
    const profile = this.personaManager.getCurrentProfile();
    
    if (!profile) {
      return {
        action: 'view',
        message: 'No persona profile loaded',
        data: null
      };
    }

    const behavior = this.personaManager.getAdaptedBehavior('view');
    const suggestions = this.personaManager.getPersonalizedSuggestions();

    return {
      action: 'view',
      profile,
      message: `Current persona: ${profile.name} (${profile.description})`,
      data: {
        preferences: profile.preferences,
        adaptedBehavior: behavior,
        personalizedSuggestions: suggestions,
        learningData: {
          commandUsage: Object.keys(profile.learningData.commandUsage).length,
          successPatterns: profile.learningData.successPatterns.length,
          errorPatterns: profile.learningData.errorPatterns.length,
          lastUpdated: profile.learningData.lastUpdated
        }
      }
    };
  }

  private async handleUpdate(updates: Record<string, any>): Promise<PersonaCommandResult> {
    if (!updates || Object.keys(updates).length === 0) {
      return {
        action: 'update',
        message: 'No updates provided. Use --key=value format to update preferences.',
        data: { availableKeys: this.getAvailablePreferenceKeys() }
      };
    }

    // Convert string values to appropriate types
    const typedUpdates: Partial<UserPreferences> = this.convertUpdateTypes(updates);
    
    await this.personaManager.updatePreferences(typedUpdates);
    
    const updatedProfile = this.personaManager.getCurrentProfile();
    
    return {
      action: 'update',
      ...(updatedProfile ? { profile: updatedProfile } : {}),
      ...(updatedProfile?.preferences ? { preferences: updatedProfile.preferences } : {}),
      message: `Updated ${Object.keys(typedUpdates).length} preference(s): ${Object.keys(typedUpdates).join(', ')}`,
      data: { updatedKeys: Object.keys(typedUpdates) }
    };
  }

  private async handleExport(outputPath?: string): Promise<PersonaCommandResult> {
    const exportData = await this.personaManager.exportPersonaData();
    
    if (outputPath) {
      const fs = await import('fs/promises');
      await fs.writeFile(outputPath, exportData);
      
      return {
        action: 'export',
        message: `Persona data exported to ${outputPath}`,
        data: { exportPath: outputPath, size: exportData.length }
      };
    } else {
      return {
        action: 'export',
        message: 'Persona data exported (returned as data)',
        data: { exportData }
      };
    }
  }

  private async handleImport(importPath: string): Promise<PersonaCommandResult> {
    if (!importPath) {
      return {
        action: 'import',
        message: 'Please provide path to persona data file: /ae:persona import <file-path>',
        data: null
      };
    }

    try {
      const fs = await import('fs/promises');
      const importData = await fs.readFile(importPath, 'utf-8');
      
      await this.personaManager.importPersonaData(importData);
      
      const importedProfile = this.personaManager.getCurrentProfile();
      
      return {
        action: 'import',
        ...(importedProfile ? { profile: importedProfile } : {}),
        message: `Persona data imported from ${importPath}`,
        data: { importPath, profileName: importedProfile?.name }
      };
    } catch (error: any) {
      throw new Error(`Failed to import persona data: ${error.message}`);
    }
  }

  private async handleReset(): Promise<PersonaCommandResult> {
    // Create a new default profile
    this.personaManager = new PersonaManager(process.cwd());
    await this.personaManager.initialize();
    
    const newProfile = this.personaManager.getCurrentProfile();
    
    return {
      action: 'reset',
      ...(newProfile ? { profile: newProfile } : {}),
      message: 'Persona profile reset to default settings',
      data: { resetAt: new Date().toISOString() }
    };
  }

  private parseUpdateOptions(args: string[]): Record<string, any> {
    const updates: Record<string, any> = {};
    
    for (const arg of args) {
      if (arg.includes('=')) {
        const [key, value] = arg.split('=', 2);
        if (key) {
          const cleanKey = key.replace(/^--/, '');
          updates[cleanKey] = value;
        }
      }
    }
    
    return updates;
  }

  private convertUpdateTypes(updates: Record<string, any>): Partial<UserPreferences> {
    const converted: Partial<UserPreferences> = {};
    
    for (const [key, value] of Object.entries(updates)) {
      switch (key) {
        case 'verbosity':
          if (['minimal', 'normal', 'detailed'].includes(value)) {
            converted.verbosity = value as UserPreferences['verbosity'];
          }
          break;
        case 'codeStyle':
          if (['functional', 'object-oriented', 'mixed'].includes(value)) {
            converted.codeStyle = value as UserPreferences['codeStyle'];
          }
          break;
        case 'explanationLevel':
          if (['beginner', 'intermediate', 'expert'].includes(value)) {
            converted.explanationLevel = value as UserPreferences['explanationLevel'];
          }
          break;
        case 'testingPreference':
          if (['unit', 'integration', 'e2e', 'all'].includes(value)) {
            converted.testingPreference = value as UserPreferences['testingPreference'];
          }
          break;
        case 'suggestionFrequency':
          if (['low', 'medium', 'high'].includes(value)) {
            converted.suggestionFrequency = value as UserPreferences['suggestionFrequency'];
          }
          break;
        case 'evidenceRequirement':
          if (['low', 'medium', 'high'].includes(value)) {
            converted.evidenceRequirement = value as UserPreferences['evidenceRequirement'];
          }
          break;
        case 'autoValidation':
          if (value === 'true' || value === 'false') {
            converted.autoValidation = value === 'true';
          }
          break;
        case 'preferredLanguages':
          converted.preferredLanguages = value.split(',').map((lang: string) => lang.trim());
          break;
        case 'preferredFrameworks':
          converted.preferredFrameworks = value.split(',').map((fw: string) => fw.trim());
          break;
      }
    }
    
    return converted;
  }

  private getAvailablePreferenceKeys(): string[] {
    return [
      'verbosity (minimal|normal|detailed)',
      'codeStyle (functional|object-oriented|mixed)',
      'explanationLevel (beginner|intermediate|expert)',
      'testingPreference (unit|integration|e2e|all)',
      'suggestionFrequency (low|medium|high)',
      'evidenceRequirement (low|medium|high)',
      'autoValidation (true|false)',
      'preferredLanguages (comma-separated)',
      'preferredFrameworks (comma-separated)'
    ];
  }

  protected override generateValidationClaim(data: PersonaCommandResult): string {
    return `Persona command execution for action '${data.action}' completed successfully`;
  }

  protected override generateSummary(data: PersonaCommandResult): string {
    return data.message;
  }
}
