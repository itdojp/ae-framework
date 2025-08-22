/**
 * Smart Persona Manager for ae-framework
 * Adapts AI behavior based on user patterns and preferences
 */

import * as fs from 'node:fs/promises';
import * as fsSync from 'node:fs';
import * as path from 'node:path';

export interface UserPreferences {
  // Communication style
  verbosity: 'minimal' | 'normal' | 'detailed';
  codeStyle: 'functional' | 'object-oriented' | 'mixed';
  explanationLevel: 'beginner' | 'intermediate' | 'expert';
  
  // Work patterns
  preferredLanguages: string[];
  preferredFrameworks: string[];
  testingPreference: 'unit' | 'integration' | 'e2e' | 'all';
  
  // AI behavior preferences
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

export class PersonaManager {
  private profilePath: string;
  private currentProfile: PersonaProfile | null = null;
  private workingContext: WorkingContext;
  private interactionCount: number = 0;
  private saveThreshold: number = 10; // Save every 10 interactions

  constructor(projectRoot: string) {
    this.profilePath = path.join(projectRoot, '.ae-framework', 'persona.json');
    this.workingContext = this.initializeWorkingContext(projectRoot);
  }

  /**
   * Initialize or load user persona profile
   */
  async initialize(): Promise<PersonaProfile> {
    try {
      const profileExists = await this.profileExists();
      if (profileExists) {
        this.currentProfile = await this.loadProfile();
      } else {
        this.currentProfile = await this.createDefaultProfile();
        await this.saveProfile();
      }
      
      return this.currentProfile;
    } catch (error) {
      console.warn('Failed to initialize persona profile, using default:', error);
      this.currentProfile = this.createEmergencyProfile();
      return this.currentProfile;
    }
  }

  /**
   * Get current persona profile
   */
  getCurrentProfile(): PersonaProfile | null {
    return this.currentProfile;
  }

  /**
   * Update working context with new command execution
   */
  updateContext(command: string, success: boolean): void {
    this.workingContext.recentCommands.unshift(command);
    if (this.workingContext.recentCommands.length > 20) {
      this.workingContext.recentCommands = this.workingContext.recentCommands.slice(0, 20);
    }

    this.workingContext.workSession.commandCount++;
    if (!success) {
      this.workingContext.workSession.errorCount++;
    }

    this.workingContext.workSession.successRate = 
      (this.workingContext.workSession.commandCount - this.workingContext.workSession.errorCount) / 
      this.workingContext.workSession.commandCount;

    // Update frequent patterns
    this.updateFrequentPatterns(command);
  }

  /**
   * Learn from user interactions and adapt preferences
   */
  async learnFromInteraction(command: string, context: any, feedback?: 'positive' | 'negative'): Promise<void> {
    if (!this.currentProfile) return;

    // Update command usage statistics
    this.currentProfile.learningData.commandUsage[command] = 
      (this.currentProfile.learningData.commandUsage[command] || 0) + 1;

    // Learn from feedback
    if (feedback === 'positive') {
      this.currentProfile.learningData.successPatterns.push(this.extractPattern(command, context));
    } else if (feedback === 'negative') {
      this.currentProfile.learningData.errorPatterns.push(this.extractPattern(command, context));
    }

    // Update time preferences
    const currentHour = new Date().getHours();
    const timeSlot = this.getTimeSlot(currentHour);
    this.currentProfile.learningData.timePreferences[timeSlot] = 
      (this.currentProfile.learningData.timePreferences[timeSlot] || 0) + 1;

    this.currentProfile.learningData.lastUpdated = new Date().toISOString();

    // Update language preferences periodically based on usage
    if (this.interactionCount % 20 === 0) { // Every 20 interactions
      this.updateLanguagePreferencesFromUsage();
    }

    // Save learning data based on interaction count
    this.interactionCount++;
    if (this.interactionCount >= this.saveThreshold) {
      this.interactionCount = 0;
      await this.saveProfile();
    }
  }

  /**
   * Get adapted behavior based on current context and learned patterns
   */
  getAdaptedBehavior(command: string, context?: any): {
    verbosity: UserPreferences['verbosity'];
    suggestionBehavior: 'proactive' | 'reactive' | 'minimal';
    evidenceLevel: 'strict' | 'normal' | 'relaxed';
    recommendations: string[];
  } {
    if (!this.currentProfile) {
      return this.getDefaultBehavior();
    }

    let adaptedVerbosity = this.currentProfile.preferences.verbosity;
    let suggestionBehavior: 'proactive' | 'reactive' | 'minimal' = 'reactive';
    let evidenceLevel: 'strict' | 'normal' | 'relaxed' = 'normal';
    const recommendations: string[] = [];

    // Apply adaptation rules
    for (const rule of this.currentProfile.adaptationRules) {
      if (this.matchesRule(rule, command, context)) {
        if (rule.adaptation.verbosity) {
          adaptedVerbosity = rule.adaptation.verbosity;
        }
        if (rule.adaptation.suggestionBehavior) {
          suggestionBehavior = rule.adaptation.suggestionBehavior;
        }
        if (rule.adaptation.evidenceLevel) {
          evidenceLevel = rule.adaptation.evidenceLevel;
        }
      }
    }

    // Context-based adaptations
    if (this.workingContext.workSession.errorCount > 3) {
      adaptedVerbosity = 'detailed';
      suggestionBehavior = 'proactive';
      recommendations.push('Consider using /ae:troubleshoot for error analysis');
    }

    if (this.workingContext.workSession.successRate > 0.9 && this.workingContext.workSession.commandCount > 10) {
      adaptedVerbosity = 'minimal';
      suggestionBehavior = 'minimal';
    }

    // Time-based adaptations
    const currentTime = this.getTimeSlot(new Date().getHours());
    if (currentTime === 'night' || currentTime === 'evening') {
      adaptedVerbosity = this.reducedVerbosity(adaptedVerbosity);
    }

    return {
      verbosity: adaptedVerbosity,
      suggestionBehavior,
      evidenceLevel,
      recommendations
    };
  }

  /**
   * Get personalized command suggestions based on context and history
   */
  getPersonalizedSuggestions(currentCommand?: string): string[] {
    if (!this.currentProfile) return [];

    const suggestions: string[] = [];
    const recentCommands = this.workingContext.recentCommands;
    const frequentPatterns = this.workingContext.frequentPatterns;

    // Suggest based on command patterns
    if (currentCommand?.includes('analyze')) {
      if (this.currentProfile.preferences.autoValidation) {
        suggestions.push('Consider adding --validate flag for evidence-based validation');
      }
    }

    // Suggest based on frequent patterns
    for (const pattern of frequentPatterns) {
      if (pattern.includes('error') && !recentCommands.some(cmd => cmd.includes('troubleshoot'))) {
        suggestions.push('Try /ae:troubleshoot for error analysis');
      }
    }

    // Suggest based on success patterns (most recent and frequent patterns first)
    const sortedSuccessPatterns = this.currentProfile.learningData.successPatterns
      .slice(-6) // Take last 6 patterns
      .reverse(); // Most recent first
    
    for (let i = 0; i < Math.min(2, sortedSuccessPatterns.length); i++) {
      const pattern = sortedSuccessPatterns[i];
      suggestions.push(`Consider: ${pattern}`);
    }

    return suggestions.slice(0, 3); // Limit to 3 suggestions
  }

  /**
   * Update user preferences based on explicit feedback
   */
  async updatePreferences(updates: Partial<UserPreferences>): Promise<void> {
    if (!this.currentProfile) return;

    this.currentProfile.preferences = {
      ...this.currentProfile.preferences,
      ...updates
    };

    await this.saveProfile();
  }

  /**
   * Export persona data for backup or migration
   */
  async exportPersonaData(): Promise<string> {
    if (!this.currentProfile) {
      throw new Error('No persona profile loaded');
    }

    return JSON.stringify({
      profile: this.currentProfile,
      context: this.workingContext,
      exportDate: new Date().toISOString()
    }, null, 2);
  }

  /**
   * Import persona data from backup
   */
  async importPersonaData(data: string): Promise<void> {
    try {
      const imported = JSON.parse(data);
      this.currentProfile = imported.profile;
      await this.saveProfile();
    } catch (error) {
      throw new Error(`Failed to import persona data: ${error}`);
    }
  }

  // Private methods

  private initializeWorkingContext(projectRoot: string): WorkingContext {
    return {
      currentProject: path.basename(projectRoot),
      recentCommands: [],
      frequentPatterns: [],
      timeOfDay: this.getTimeSlot(new Date().getHours()),
      workSession: {
        startTime: new Date().toISOString(),
        commandCount: 0,
        errorCount: 0,
        successRate: 1.0
      }
    };
  }

  private async profileExists(): Promise<boolean> {
    try {
      await fs.access(this.profilePath);
      return true;
    } catch {
      return false;
    }
  }

  private async loadProfile(): Promise<PersonaProfile> {
    const data = await fs.readFile(this.profilePath, 'utf-8');
    return JSON.parse(data);
  }

  private async saveProfile(): Promise<void> {
    if (!this.currentProfile) return;

    const dir = path.dirname(this.profilePath);
    await fs.mkdir(dir, { recursive: true });
    await fs.writeFile(this.profilePath, JSON.stringify(this.currentProfile, null, 2));
  }

  private async createDefaultProfile(): Promise<PersonaProfile> {
    return {
      id: `persona-${Date.now()}`,
      name: 'Default Developer',
      description: 'Default persona profile for new users',
      preferences: {
        verbosity: 'normal',
        codeStyle: 'mixed',
        explanationLevel: 'intermediate',
        preferredLanguages: this.inferInitialLanguagePreferences(),
        preferredFrameworks: [],
        testingPreference: 'all',
        suggestionFrequency: 'medium',
        autoValidation: false,
        evidenceRequirement: 'medium'
      },
      adaptationRules: [
        {
          trigger: { command: 'troubleshoot' },
          adaptation: { verbosity: 'detailed', suggestionBehavior: 'proactive' },
          confidence: 0.8
        },
        {
          trigger: { context: { workSession: { 
            startTime: new Date().toISOString(),
            commandCount: 10,
            errorCount: 1,
            successRate: 0.95 
          } } },
          adaptation: { verbosity: 'minimal', suggestionBehavior: 'minimal' },
          confidence: 0.7
        }
      ],
      learningData: {
        commandUsage: {},
        successPatterns: [],
        errorPatterns: [],
        timePreferences: {},
        lastUpdated: new Date().toISOString()
      }
    };
  }

  private createEmergencyProfile(): PersonaProfile {
    return {
      id: 'emergency-profile',
      name: 'Emergency Profile',
      description: 'Fallback profile when loading fails',
      preferences: {
        verbosity: 'normal',
        codeStyle: 'mixed',
        explanationLevel: 'intermediate',
        preferredLanguages: [],
        preferredFrameworks: [],
        testingPreference: 'all',
        suggestionFrequency: 'medium',
        autoValidation: false,
        evidenceRequirement: 'medium'
      },
      adaptationRules: [],
      learningData: {
        commandUsage: {},
        successPatterns: [],
        errorPatterns: [],
        timePreferences: {},
        lastUpdated: new Date().toISOString()
      }
    };
  }

  private updateFrequentPatterns(command: string): void {
    const pattern = this.extractCommandPattern(command);
    const existingIndex = this.workingContext.frequentPatterns.indexOf(pattern);
    
    if (existingIndex >= 0) {
      // Move to front
      this.workingContext.frequentPatterns.splice(existingIndex, 1);
      this.workingContext.frequentPatterns.unshift(pattern);
    } else {
      this.workingContext.frequentPatterns.unshift(pattern);
      if (this.workingContext.frequentPatterns.length > 10) {
        this.workingContext.frequentPatterns = this.workingContext.frequentPatterns.slice(0, 10);
      }
    }
  }

  private extractPattern(command: string, context: any): string {
    return `${command}:${JSON.stringify(context).substring(0, 100)}`;
  }

  private extractCommandPattern(command: string): string {
    return command.split(' ')[0] || ''; // Just the base command
  }

  private getTimeSlot(hour: number): 'morning' | 'afternoon' | 'evening' | 'night' {
    if (hour >= 6 && hour < 12) return 'morning';
    if (hour >= 12 && hour < 18) return 'afternoon';
    if (hour >= 18 && hour < 22) return 'evening';
    return 'night';
  }

  private matchesRule(rule: AdaptationRule, command: string, context: any): boolean {
    if (rule.trigger.command && !command.includes(rule.trigger.command)) {
      return false;
    }
    
    if (rule.trigger.pattern && !rule.trigger.pattern.test(command)) {
      return false;
    }
    
    if (rule.trigger.context) {
      // Enhanced context matching with specific property checks
      const contextMatch = Object.keys(rule.trigger.context).every(key => {
        const expectedValue = (rule.trigger.context as any)[key];
        const actualValue = this.getContextValue(key);
        return this.compareContextValues(actualValue, expectedValue);
      });
      if (!contextMatch) return false;
    }
    
    // Use confidence threshold instead of random - more deterministic
    return rule.confidence >= 0.5; // Apply rules with confidence >= 50%
  }

  private getContextValue(keyPath: string): any {
    const keys = keyPath.split('.');
    let value: any = this.workingContext;
    for (const key of keys) {
      value = value?.[key];
    }
    return value;
  }

  private compareContextValues(actual: any, expected: any): boolean {
    if (typeof expected === 'number' && typeof actual === 'number') {
      return actual >= expected * 0.9; // Allow 10% tolerance for numeric values
    }
    return actual === expected;
  }

  private reducedVerbosity(verbosity: UserPreferences['verbosity']): UserPreferences['verbosity'] {
    switch (verbosity) {
      case 'detailed': return 'normal';
      case 'normal': return 'minimal';
      case 'minimal': return 'minimal';
      default: return verbosity;
    }
  }

  private getDefaultBehavior(): {
    verbosity: UserPreferences['verbosity'];
    suggestionBehavior: 'proactive' | 'reactive' | 'minimal';
    evidenceLevel: 'strict' | 'normal' | 'relaxed';
    recommendations: string[];
  } {
    return {
      verbosity: 'normal',
      suggestionBehavior: 'reactive',
      evidenceLevel: 'normal',
      recommendations: []
    };
  }

  private inferInitialLanguagePreferences(): string[] {
    // Analyze project structure to infer language preferences
    try {
      const projectDir = path.dirname(this.profilePath);
      
      const languageIndicators: { [key: string]: string[] } = {
        'typescript': ['tsconfig.json', '*.ts', '*.tsx', 'package.json'],
        'javascript': ['package.json', '*.js', '*.jsx', '.babelrc'],
        'python': ['requirements.txt', '*.py', 'setup.py', 'pyproject.toml'],
        'java': ['pom.xml', 'build.gradle', '*.java'],
        'go': ['go.mod', '*.go'],
        'rust': ['Cargo.toml', '*.rs'],
        'elixir': ['mix.exs', '*.ex', '*.exs', 'config/config.exs', 'lib/', 'test/']
      };

      const detectedLanguages: string[] = [];

      for (const [language, indicators] of Object.entries(languageIndicators)) {
        for (const indicator of indicators) {
          try {
            if (indicator.includes('.')) {
              if (fsSync.existsSync(path.join(projectDir, indicator))) {
                detectedLanguages.push(language);
                break;
              }
            }
          } catch {
            // Ignore file system errors
          }
        }
      }

      return detectedLanguages.length > 0 ? detectedLanguages : ['typescript', 'javascript'];
    } catch {
      // Fallback to common languages if analysis fails
      return ['typescript', 'javascript'];
    }
  }

  /**
   * Update language preferences based on actual command usage patterns
   */
  private updateLanguagePreferencesFromUsage(): void {
    if (!this.currentProfile) return;

    const languageUsage: { [key: string]: number } = {};
    
    // Analyze command usage to detect language patterns
    for (const [command, count] of Object.entries(this.currentProfile.learningData.commandUsage)) {
      const languageHints = this.extractLanguageHints(command);
      for (const lang of languageHints) {
        languageUsage[lang] = (languageUsage[lang] || 0) + count;
      }
    }

    // Update preferences based on usage frequency
    const sortedLanguages = Object.entries(languageUsage)
      .sort(([,a], [,b]) => b - a)
      .map(([lang]) => lang);

    if (sortedLanguages.length > 0) {
      this.currentProfile.preferences.preferredLanguages = [
        ...sortedLanguages.slice(0, 3), // Top 3 used languages
        ...this.currentProfile.preferences.preferredLanguages.filter(
          lang => !sortedLanguages.includes(lang)
        )
      ].slice(0, 5); // Keep max 5 languages
    }
  }

  private extractLanguageHints(command: string): string[] {
    const hints: string[] = [];
    
    if (command.includes('.ts') || command.includes('typescript')) hints.push('typescript');
    if (command.includes('.js') || command.includes('javascript')) hints.push('javascript');
    if (command.includes('.py') || command.includes('python')) hints.push('python');
    if (command.includes('.java')) hints.push('java');
    if (command.includes('.go')) hints.push('go');
    if (command.includes('.rs') || command.includes('rust')) hints.push('rust');
    if (command.includes('.ex') || command.includes('.exs') || command.includes('elixir') || command.includes('mix')) hints.push('elixir');
    
    return hints;
  }
}