import { describe, test, expect, beforeEach, vi } from 'vitest';
import { PersonaCommand } from '../../src/commands/extended/persona-command.js';
import { PersonaManager } from '../../src/utils/persona-manager.js';
import type { CommandContext } from '../../src/commands/slash-command-manager.js';

// Mock PersonaManager
vi.mock('../../src/utils/persona-manager.js');

describe('PersonaCommand', () => {
  let personaCommand: PersonaCommand;
  let mockPersonaManager: any;
  let mockContext: CommandContext;

  beforeEach(() => {
    vi.clearAllMocks();
    
    // Create mock persona manager
    mockPersonaManager = {
      initialize: vi.fn().mockResolvedValue({
        id: 'test-profile',
        name: 'Test User',
        description: 'Test profile',
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
          successPatterns: ['pattern1'],
          errorPatterns: ['pattern2'],
          timePreferences: { morning: 10 },
          lastUpdated: '2023-01-01T00:00:00.000Z'
        }
      }),
      getCurrentProfile: vi.fn().mockReturnValue({
        id: 'test-profile',
        name: 'Test User',
        description: 'Test profile',
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
          successPatterns: ['pattern1'],
          errorPatterns: ['pattern2'],
          timePreferences: { morning: 10 },
          lastUpdated: '2023-01-01T00:00:00.000Z'
        }
      }),
      getAdaptedBehavior: vi.fn().mockReturnValue({
        verbosity: 'normal',
        suggestionBehavior: 'reactive',
        evidenceLevel: 'normal',
        recommendations: []
      }),
      getPersonalizedSuggestions: vi.fn().mockReturnValue(['Suggestion 1', 'Suggestion 2']),
      updatePreferences: vi.fn().mockResolvedValue(undefined),
      exportPersonaData: vi.fn().mockResolvedValue(JSON.stringify({ test: 'data' })),
      importPersonaData: vi.fn().mockResolvedValue(undefined)
    };

    vi.mocked(PersonaManager).mockImplementation(() => mockPersonaManager);

    personaCommand = new PersonaCommand();

    mockContext = {
      phaseStateManager: {} as any,
      steeringLoader: {} as any,
      approvalService: {} as any,
      projectRoot: '/test/project'
    };
  });

  describe('command registration', () => {
    test('should have correct command properties', () => {
      expect(personaCommand.name).toBe('/ae:persona');
      expect(personaCommand.description).toContain('Smart Persona System');
      expect(personaCommand.aliases).toContain('/persona');
      expect(personaCommand.aliases).toContain('/a:persona');
    });
  });

  describe('argument validation', () => {
    test('should accept empty arguments (defaults to view)', async () => {
      const validation = (personaCommand as any).validateArgs([]);
      
      expect(validation.isValid).toBe(true);
    });

    test('should accept valid actions', async () => {
      const validActions = ['view', 'update', 'export', 'import', 'reset'];
      
      for (const action of validActions) {
        const validation = (personaCommand as any).validateArgs([action]);
        expect(validation.isValid).toBe(true);
      }
    });

    test('should reject invalid actions', async () => {
      const validation = (personaCommand as any).validateArgs(['invalid']);
      
      expect(validation.isValid).toBe(false);
      expect(validation.message).toContain('Invalid action');
    });
  });

  describe('view action', () => {
    test('should display current persona profile', async () => {
      const result = await personaCommand.handler([], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Test User');
      expect(result.data?.action).toBe('view');
      expect(result.data?.profile).toBeDefined();
      expect(result.data?.data?.preferences).toBeDefined();
      expect(mockPersonaManager.initialize).toHaveBeenCalled();
      expect(mockPersonaManager.getAdaptedBehavior).toHaveBeenCalledWith('view');
      expect(mockPersonaManager.getPersonalizedSuggestions).toHaveBeenCalled();
    });

    test('should handle case when no profile is loaded', async () => {
      mockPersonaManager.getCurrentProfile.mockReturnValue(null);

      const result = await personaCommand.handler(['view'], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('No persona profile loaded');
      expect(result.data?.profile).toBeUndefined();
    });
  });

  describe('update action', () => {
    test('should update preferences with valid values', async () => {
      const result = await personaCommand.handler([
        'update',
        '--verbosity=detailed',
        '--autoValidation=true',
        '--preferredLanguages=typescript,rust'
      ], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Updated');
      expect(result.data?.action).toBe('update');
      expect(mockPersonaManager.updatePreferences).toHaveBeenCalledWith({
        verbosity: 'detailed',
        autoValidation: true,
        preferredLanguages: ['typescript', 'rust']
      });
    });

    test('should show available keys when no updates provided', async () => {
      const result = await personaCommand.handler(['update'], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('No updates provided');
      expect(result.data?.data?.availableKeys).toBeDefined();
    });

    test('should ignore invalid preference values', async () => {
      const result = await personaCommand.handler([
        'update',
        '--verbosity=invalid',
        '--autoValidation=maybe'
      ], mockContext);

      expect(result.success).toBe(true);
      expect(mockPersonaManager.updatePreferences).toHaveBeenCalledWith({});
    });
  });

  describe('export action', () => {
    test('should export persona data without file path', async () => {
      const result = await personaCommand.handler(['export'], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('exported');
      expect(result.data?.action).toBe('export');
      expect(result.data?.data?.exportData).toBeDefined();
      expect(mockPersonaManager.exportPersonaData).toHaveBeenCalled();
    });

    test('should export persona data to file', async () => {
      vi.doMock('fs/promises', () => ({
        writeFile: vi.fn().mockResolvedValue(undefined)
      }));

      const result = await personaCommand.handler(['export', '--output=/test/export.json'], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('exported to');
      expect(result.data?.data?.exportPath).toBe('/test/export.json');
    });
  });

  describe('import action', () => {
    test('should import persona data from file', async () => {
      vi.doMock('fs/promises', () => ({
        readFile: vi.fn().mockResolvedValue(JSON.stringify({ test: 'import data' }))
      }));

      const result = await personaCommand.handler(['import', '/test/import.json'], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('imported from');
      expect(result.data?.action).toBe('import');
      expect(mockPersonaManager.importPersonaData).toHaveBeenCalled();
    });

    test('should show error when no import path provided', async () => {
      const result = await personaCommand.handler(['import'], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Please provide path');
      expect(result.data?.data).toBeNull();
    });

    test('should handle import errors', async () => {
      vi.doMock('fs/promises', () => ({
        readFile: vi.fn().mockRejectedValue(new Error('File not found'))
      }));

      const result = await personaCommand.handler(['import', '/invalid/path.json'], mockContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('failed');
    });
  });

  describe('reset action', () => {
    test('should reset persona profile to defaults', async () => {
      const result = await personaCommand.handler(['reset'], mockContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('reset to default');
      expect(result.data?.action).toBe('reset');
      expect(result.data?.data?.resetAt).toBeDefined();
    });
  });

  describe('error handling', () => {
    test('should handle persona manager initialization failure', async () => {
      mockPersonaManager.initialize.mockRejectedValue(new Error('Init failed'));

      const result = await personaCommand.handler(['view'], mockContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Persona command failed');
    });

    test('should handle update failures', async () => {
      mockPersonaManager.updatePreferences.mockRejectedValue(new Error('Update failed'));

      const result = await personaCommand.handler(['update', '--verbosity=detailed'], mockContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Persona command failed');
    });
  });

  describe('option parsing', () => {
    test('should parse update options correctly', () => {
      const parseUpdateOptions = (personaCommand as any).parseUpdateOptions.bind(personaCommand);
      
      const options = parseUpdateOptions(['--verbosity=minimal', '--autoValidation=false']);
      
      expect(options).toEqual({
        verbosity: 'minimal',
        autoValidation: 'false'
      });
    });

    test('should convert string values to appropriate types', () => {
      const convertUpdateTypes = (personaCommand as any).convertUpdateTypes.bind(personaCommand);
      
      const converted = convertUpdateTypes({
        verbosity: 'detailed',
        autoValidation: 'true',
        preferredLanguages: 'typescript,javascript',
        invalid: 'value'
      });
      
      expect(converted).toEqual({
        verbosity: 'detailed',
        autoValidation: true,
        preferredLanguages: ['typescript', 'javascript']
      });
    });

    test('should get available preference keys', () => {
      const getAvailablePreferenceKeys = (personaCommand as any).getAvailablePreferenceKeys.bind(personaCommand);
      
      const keys = getAvailablePreferenceKeys();
      
      expect(Array.isArray(keys)).toBe(true);
      expect(keys.length).toBeGreaterThan(0);
      expect(keys.some(key => key.includes('verbosity'))).toBe(true);
    });
  });
});