import { describe, test, expect, beforeEach, vi } from 'vitest';
import { PersonaIntegrationService } from '../../src/services/persona-integration.js';
import { PersonaManager } from '../../src/utils/persona-manager.js';
import type { CommandResult } from '../../src/commands/slash-command-manager.js';

// Mock PersonaManager
vi.mock('../../src/utils/persona-manager.js');

describe('PersonaIntegrationService', () => {
  let personaService: PersonaIntegrationService;
  let mockPersonaManager: any;
  const testProjectRoot = '/test/project';

  beforeEach(() => {
    vi.clearAllMocks();
    
    // Create mock persona manager
    mockPersonaManager = {
      initialize: vi.fn().mockResolvedValue(undefined),
      getCurrentProfile: vi.fn().mockReturnValue({
        id: 'test-profile',
        name: 'Test User',
        preferences: {
          verbosity: 'normal',
          codeStyle: 'mixed',
          explanationLevel: 'intermediate',
          preferredLanguages: ['typescript'],
          preferredFrameworks: ['react'],
          testingPreference: 'all',
          suggestionFrequency: 'medium',
          autoValidation: true,
          evidenceRequirement: 'medium'
        },
        learningData: {
          commandUsage: { '/ae:analyze': 5 },
          successPatterns: ['analyze:success'],
          errorPatterns: ['troubleshoot:error'],
          timePreferences: { morning: 10 },
          lastUpdated: new Date().toISOString()
        }
      }),
      getAdaptedBehavior: vi.fn().mockReturnValue({
        verbosity: 'normal',
        suggestionBehavior: 'reactive',
        evidenceLevel: 'normal',
        recommendations: ['Try using --validate flag']
      }),
      getPersonalizedSuggestions: vi.fn().mockReturnValue(['Consider security analysis']),
      updateContext: vi.fn(),
      learnFromInteraction: vi.fn().mockResolvedValue(undefined),
      updatePreferences: vi.fn().mockResolvedValue(undefined)
    };

    vi.mocked(PersonaManager).mockImplementation(() => mockPersonaManager);
    personaService = new PersonaIntegrationService(testProjectRoot);
  });

  describe('initialization', () => {
    test('should initialize persona manager', async () => {
      await personaService.initialize();

      expect(mockPersonaManager.initialize).toHaveBeenCalled();
    });
  });

  describe('command behavior adaptation', () => {
    test('should adapt command behavior based on persona preferences', async () => {
      const adaptedBehavior = await personaService.adaptCommandBehavior('/ae:analyze test.ts');

      expect(adaptedBehavior).toBeDefined();
      expect(adaptedBehavior.verbosity).toBe('normal');
      expect(adaptedBehavior.includeExplanations).toBe(true);
      expect(adaptedBehavior.suggestionLevel).toBe('moderate');
      expect(adaptedBehavior.evidenceValidation).toBe(false);
      expect(mockPersonaManager.getAdaptedBehavior).toHaveBeenCalledWith('/ae:analyze test.ts', undefined);
    });

    test('should include proactive suggestions when behavior is proactive', async () => {
      mockPersonaManager.getAdaptedBehavior.mockReturnValue({
        verbosity: 'detailed',
        suggestionBehavior: 'proactive',
        evidenceLevel: 'normal',
        recommendations: []
      });

      const adaptedBehavior = await personaService.adaptCommandBehavior('/ae:troubleshoot');

      expect(adaptedBehavior.suggestionLevel).toBe('comprehensive');
      expect(adaptedBehavior.proactiveSuggestions).toEqual(['Consider security analysis']);
    });

    test('should enable evidence validation for strict evidence level', async () => {
      mockPersonaManager.getAdaptedBehavior.mockReturnValue({
        verbosity: 'normal',
        suggestionBehavior: 'reactive',
        evidenceLevel: 'strict',
        recommendations: []
      });

      const adaptedBehavior = await personaService.adaptCommandBehavior('/ae:analyze');

      expect(adaptedBehavior.evidenceValidation).toBe(true);
    });
  });

  describe('learning from execution', () => {
    test('should learn from successful command execution', async () => {
      await personaService.initialize(); // Initialize first
      
      const result: CommandResult = {
        success: true,
        message: 'Analysis complete',
        data: { findings: [] }
      };

      await personaService.learnFromExecution('/ae:analyze', result, { file: 'test.ts' }, 'positive');

      expect(mockPersonaManager.updateContext).toHaveBeenCalledWith('/ae:analyze', true);
      expect(mockPersonaManager.learnFromInteraction).toHaveBeenCalledWith(
        '/ae:analyze',
        { file: 'test.ts' },
        'positive'
      );
    });

    test('should learn from failed command execution', async () => {
      await personaService.initialize();
      const result: CommandResult = {
        success: false,
        message: 'Analysis failed'
      };

      await personaService.learnFromExecution('/ae:analyze', result, undefined, 'negative');

      expect(mockPersonaManager.updateContext).toHaveBeenCalledWith('/ae:analyze', false);
      expect(mockPersonaManager.learnFromInteraction).toHaveBeenCalledWith(
        '/ae:analyze',
        undefined,
        'negative'
      );
    });
  });

  describe('command result adaptation', () => {
    test('should minimize message for minimal verbosity', async () => {
      const result: CommandResult = {
        success: true,
        message: 'Analysis complete\nFound 5 issues\nGenerated detailed report',
        data: {}
      };

      const adaptedBehavior = {
        verbosity: 'minimal' as const,
        includeExplanations: false,
        suggestionLevel: 'minimal' as const,
        evidenceValidation: false,
        proactiveSuggestions: []
      };

      const adaptedResult = await personaService.adaptCommandResult(result, '/ae:analyze', adaptedBehavior);

      expect(adaptedResult.message).toBe('Found 5 issues');
    });

    test('should enhance message for detailed verbosity', async () => {
      const result: CommandResult = {
        success: true,
        message: 'Analysis complete',
        data: {}
      };

      const adaptedBehavior = {
        verbosity: 'detailed' as const,
        includeExplanations: true,
        suggestionLevel: 'comprehensive' as const,
        evidenceValidation: false,
        proactiveSuggestions: []
      };

      const adaptedResult = await personaService.adaptCommandResult(result, '/ae:analyze', adaptedBehavior);

      expect(adaptedResult.message).toContain('Tip:');
      expect(adaptedResult.message).toContain('--security flag');
    });

    test('should add proactive suggestions to result data', async () => {
      const result: CommandResult = {
        success: true,
        message: 'Analysis complete',
        data: { issues: [] }
      };

      const adaptedBehavior = {
        verbosity: 'normal' as const,
        includeExplanations: true,
        suggestionLevel: 'comprehensive' as const,
        evidenceValidation: false,
        proactiveSuggestions: ['Try security analysis', 'Consider performance check']
      };

      const adaptedResult = await personaService.adaptCommandResult(result, '/ae:analyze', adaptedBehavior);

      expect(adaptedResult.data?.personaSuggestions).toEqual(['Try security analysis', 'Consider performance check']);
    });
  });

  describe('validation options', () => {
    test('should return validation options based on persona preferences', async () => {
      await personaService.initialize();
      const options = personaService.getValidationOptions('/ae:analyze');

      expect(options.validate).toBe(true); // autoValidation is true in mock
      expect(options.minConfidence).toBe(0.7); // normal evidence level
    });

    test('should adjust confidence level for strict evidence requirement', async () => {
      await personaService.initialize();
      mockPersonaManager.getAdaptedBehavior.mockReturnValue({
        evidenceLevel: 'strict'
      });
      mockPersonaManager.getCurrentProfile.mockReturnValue({
        preferences: { autoValidation: false }
      });

      const options = personaService.getValidationOptions('/ae:analyze');

      expect(options.validate).toBe(true); // strict evidence forces validation
      expect(options.minConfidence).toBe(0.9); // strict evidence level
    });

    test('should return relaxed validation for relaxed evidence level', async () => {
      await personaService.initialize();
      mockPersonaManager.getAdaptedBehavior.mockReturnValue({
        evidenceLevel: 'relaxed'
      });
      mockPersonaManager.getCurrentProfile.mockReturnValue({
        preferences: { autoValidation: false }
      });

      const options = personaService.getValidationOptions('/ae:analyze');

      expect(options.validate).toBe(false); // no auto-validation and relaxed
      expect(options.minConfidence).toBe(0.5); // relaxed evidence level
    });
  });

  describe('personalized command options', () => {
    test('should return language preferences for analyze commands', async () => {
      await personaService.initialize();
      const options = personaService.getPersonalizedCommandOptions('/ae:analyze');

      expect(options.languages).toEqual(['typescript']);
    });

    test('should return code style preferences for generate commands', async () => {
      await personaService.initialize();
      const options = personaService.getPersonalizedCommandOptions('/ae:generate');

      expect(options.testingStyle).toBe('all');
      expect(options.codeStyle).toBe('mixed');
    });

    test('should return explanation level for document commands', async () => {
      await personaService.initialize();
      const options = personaService.getPersonalizedCommandOptions('/ae:document');

      expect(options.explanationLevel).toBe('intermediate');
    });

    test('should return empty options when not initialized', () => {
      const uninitializedService = new PersonaIntegrationService('/test');
      const options = uninitializedService.getPersonalizedCommandOptions('/ae:analyze');

      expect(options).toEqual({});
    });
  });

  describe('contextual help', () => {
    test('should provide help based on error patterns', () => {
      const help = personaService.getContextualHelp('/ae:troubleshoot', 'module not found');

      expect(Array.isArray(help)).toBe(true);
    });

    test('should provide help based on success patterns', () => {
      const help = personaService.getContextualHelp('/ae:analyze');

      expect(Array.isArray(help)).toBe(true);
    });

    test('should return empty array when not initialized', () => {
      const uninitializedService = new PersonaIntegrationService('/test');
      const help = uninitializedService.getContextualHelp('/ae:analyze');

      expect(help).toEqual([]);
    });
  });

  describe('preference updates from usage', () => {
    test('should update preferences based on command usage patterns', async () => {
      await personaService.initialize();
      await personaService.updatePreferencesFromUsage();

      // Should analyze command usage and potentially update preferences
      expect(mockPersonaManager.getCurrentProfile).toHaveBeenCalled();
    });
  });

  describe('persona manager access', () => {
    test('should provide access to persona manager', () => {
      const manager = personaService.getPersonaManager();

      expect(manager).toBeDefined();
      expect(manager).toBe(mockPersonaManager);
    });
  });
});