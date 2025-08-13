import { describe, test, expect, beforeEach, vi } from 'vitest';
import { InstallerCommand } from '../../src/commands/extended/installer-command.js';
import { InstallerManager } from '../../src/utils/installer-manager.js';
import { ContextManager } from '../../src/utils/context-manager.js';
import * as fs from 'fs/promises';

// Mock dependencies
vi.mock('fs/promises');
vi.mock('../../src/utils/installer-manager.js');
vi.mock('../../src/utils/context-manager.js');
vi.mock('child_process');

describe('InstallerCommand', () => {
  let installerCommand: InstallerCommand;
  let mockInstallerManager: any;
  let mockContextManager: any;
  const testContext = { projectRoot: '/test/project' };

  beforeEach(() => {
    vi.clearAllMocks();
    
    // Mock InstallerManager
    mockInstallerManager = {
      getAvailableTemplates: vi.fn(),
      getTemplate: vi.fn(),
      getTemplatesByCategory: vi.fn(),
      installTemplate: vi.fn(),
      suggestTemplates: vi.fn(),
      createCustomTemplate: vi.fn()
    };
    vi.mocked(InstallerManager).mockImplementation(() => mockInstallerManager);

    // Mock ContextManager
    mockContextManager = {
      updateContext: vi.fn()
    };
    vi.mocked(ContextManager).mockImplementation(() => mockContextManager);

    // Mock file system
    vi.mocked(fs.access).mockResolvedValue(undefined);
    vi.mocked(fs.mkdir).mockResolvedValue(undefined);
    vi.mocked(fs.writeFile).mockResolvedValue(undefined);

    installerCommand = new InstallerCommand();
  });

  describe('Command Registration', () => {
    test('should have correct command properties', () => {
      expect(installerCommand.name).toBe('/ae:installer');
      expect(installerCommand.description).toContain('Install project templates');
      expect(installerCommand.category).toBe('utility');
      expect(installerCommand.aliases).toContain('/installer');
      expect(installerCommand.aliases).toContain('/install');
    });
  });

  describe('List Templates', () => {
    test('should list all available templates', async () => {
      const mockTemplates = [
        {
          id: 'typescript-node',
          name: 'TypeScript Node.js',
          description: 'Node.js project with TypeScript',
          category: 'api',
          language: 'typescript',
          dependencies: [],
          scripts: {},
          files: [],
          configurations: []
        },
        {
          id: 'react-vite',
          name: 'React + Vite',
          description: 'React app with Vite',
          category: 'web',
          language: 'typescript',
          framework: 'react',
          dependencies: [],
          scripts: {},
          files: [],
          configurations: []
        }
      ];

      mockInstallerManager.getAvailableTemplates.mockReturnValue(mockTemplates);

      const result = await installerCommand.handler(['list'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Available Templates');
      expect(result.message).toContain('typescript-node');
      expect(result.message).toContain('react-vite');
      expect(result.availableTemplates).toEqual(mockTemplates);
    });

    test('should handle templates command alias', async () => {
      mockInstallerManager.getAvailableTemplates.mockReturnValue([]);

      const result = await installerCommand.handler(['templates'], testContext);

      expect(result.success).toBe(true);
      expect(mockInstallerManager.getAvailableTemplates).toHaveBeenCalled();
    });
  });

  describe('Suggest Templates', () => {
    test('should provide template suggestions', async () => {
      const mockSuggestions = {
        suggestions: ['typescript-node', 'express-api'],
        reasoning: ['TypeScript files detected', 'API project structure found']
      };

      mockInstallerManager.suggestTemplates.mockResolvedValue(mockSuggestions);

      const result = await installerCommand.handler(['suggest'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Template Suggestions');
      expect(result.suggestions).toEqual(mockSuggestions.suggestions);
      expect(result.evidence).toEqual(mockSuggestions.reasoning);
    });

    test('should handle no suggestions available', async () => {
      mockInstallerManager.suggestTemplates.mockResolvedValue({
        suggestions: [],
        reasoning: ['No specific patterns detected']
      });

      const result = await installerCommand.handler(['suggest'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('No specific suggestions');
    });
  });

  describe('Template Installation', () => {
    test('should install template successfully', async () => {
      const mockTemplate = {
        id: 'typescript-node',
        name: 'TypeScript Node.js',
        description: 'TypeScript Node.js project',
        category: 'api',
        language: 'typescript',
        dependencies: [],
        scripts: { dev: 'tsx src/index.ts' },
        files: [],
        configurations: []
      };

      const mockInstallResult = {
        success: true,
        message: 'Installation successful',
        installedDependencies: ['typescript', '@types/node'],
        createdFiles: ['src/index.ts', 'package.json'],
        configuredFiles: ['tsconfig.json'],
        executedSteps: ['Setup TypeScript configuration'],
        warnings: [],
        errors: [],
        duration: 5000
      };

      mockInstallerManager.getTemplate.mockReturnValue(mockTemplate);
      mockInstallerManager.installTemplate.mockResolvedValue(mockInstallResult);

      const result = await installerCommand.handler(['typescript-node'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Successfully installed');
      expect(result.installedTemplate).toBe('typescript-node');
      expect(result.installedDependencies).toEqual(mockInstallResult.installedDependencies);
      expect(result.createdFiles).toEqual(mockInstallResult.createdFiles);
      expect(mockContextManager.updateContext).toHaveBeenCalledWith({
        installedTemplate: 'typescript-node',
        templateCategory: 'api',
        projectLanguage: 'typescript',
        projectFramework: undefined
      });
    });

    test('should handle non-existent template', async () => {
      mockInstallerManager.getTemplate.mockReturnValue(undefined);
      mockInstallerManager.getAvailableTemplates.mockReturnValue([
        { id: 'existing-template', name: 'Existing Template' }
      ]);
      mockInstallerManager.suggestTemplates.mockResolvedValue({
        suggestions: ['suggested-template'],
        reasoning: ['Based on project analysis']
      });

      const result = await installerCommand.handler(['non-existent'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Template \'non-existent\' not found');
      expect(result.message).toContain('Available templates');
    });

    test('should handle installation failure', async () => {
      const mockTemplate = {
        id: 'failing-template',
        name: 'Failing Template',
        description: 'Template that fails to install',
        category: 'api',
        language: 'typescript',
        dependencies: [],
        scripts: {},
        files: [],
        configurations: []
      };

      const mockInstallResult = {
        success: false,
        message: 'Installation failed',
        installedDependencies: [],
        createdFiles: [],
        configuredFiles: [],
        executedSteps: [],
        warnings: ['Some warning'],
        errors: ['Installation error', 'Dependency error'],
        duration: 2000
      };

      mockInstallerManager.getTemplate.mockReturnValue(mockTemplate);
      mockInstallerManager.installTemplate.mockResolvedValue(mockInstallResult);

      const result = await installerCommand.handler(['failing-template'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Failed to install template');
      expect(result.message).toContain('Installation error');
      expect(result.message).toContain('Dependency error');
    });

    test('should parse installation options correctly', async () => {
      const mockTemplate = {
        id: 'typescript-node',
        name: 'TypeScript Node.js',
        category: 'api',
        language: 'typescript',
        dependencies: [],
        scripts: {},
        files: [],
        configurations: []
      };

      const mockInstallResult = {
        success: true,
        message: 'Installation successful',
        installedDependencies: [],
        createdFiles: [],
        configuredFiles: [],
        executedSteps: [],
        warnings: [],
        errors: [],
        duration: 1000
      };

      mockInstallerManager.getTemplate.mockReturnValue(mockTemplate);
      mockInstallerManager.installTemplate.mockResolvedValue(mockInstallResult);

      await installerCommand.handler([
        'typescript-node',
        '--name=my-project',
        '--packageManager=pnpm'
      ], testContext);

      expect(mockInstallerManager.installTemplate).toHaveBeenCalledWith(
        'typescript-node',
        expect.objectContaining({
          projectName: 'my-project',
          packageManager: 'pnpm'
        })
      );
    });
  });

  describe('Help Command', () => {
    test('should display help information', async () => {
      const result = await installerCommand.handler(['help'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Installer Command Help');
      expect(result.message).toContain('/ae:installer <action>');
      expect(result.message).toContain('list/templates');
      expect(result.message).toContain('suggest');
    });
  });

  describe('Error Handling', () => {
    test('should handle missing action', async () => {
      const result = await installerCommand.handler([], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('No action specified');
    });

    test('should handle installer manager errors', async () => {
      mockInstallerManager.getAvailableTemplates.mockImplementation(() => {
        throw new Error('Manager error');
      });

      const result = await installerCommand.handler(['list'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Failed to list templates');
      expect(result.message).toContain('Manager error');
    });
  });

  describe('Recommendations', () => {
    test('should generate post-installation recommendations for TypeScript', async () => {
      const mockTemplate = {
        id: 'typescript-node',
        name: 'TypeScript Node.js',
        category: 'api',
        language: 'typescript',
        dependencies: [],
        scripts: { 'type-check': 'tsc --noEmit' },
        files: [],
        configurations: []
      };

      const mockInstallResult = {
        success: true,
        message: 'Installation successful',
        installedDependencies: ['typescript'],
        createdFiles: ['src/index.ts'],
        configuredFiles: [],
        executedSteps: [],
        warnings: [],
        errors: [],
        duration: 1000
      };

      mockInstallerManager.getTemplate.mockReturnValue(mockTemplate);
      mockInstallerManager.installTemplate.mockResolvedValue(mockInstallResult);

      const result = await installerCommand.handler(['typescript-node'], testContext);

      expect(result.success).toBe(true);
      expect(result.recommendations).toContain('Run type checking with npm run type-check or similar');
      expect(result.recommendations).toContain('Available npm scripts: type-check');
    });

    test('should generate framework-specific recommendations', async () => {
      const mockTemplate = {
        id: 'react-vite',
        name: 'React + Vite',
        category: 'web',
        language: 'typescript',
        framework: 'react',
        dependencies: [],
        scripts: { dev: 'vite' },
        files: [],
        configurations: []
      };

      const mockInstallResult = {
        success: true,
        message: 'Installation successful',
        installedDependencies: ['react', 'vite'],
        createdFiles: ['src/App.tsx'],
        configuredFiles: [],
        executedSteps: [],
        warnings: [],
        errors: [],
        duration: 1000
      };

      mockInstallerManager.getTemplate.mockReturnValue(mockTemplate);
      mockInstallerManager.installTemplate.mockResolvedValue(mockInstallResult);

      const result = await installerCommand.handler(['react-vite'], testContext);

      expect(result.success).toBe(true);
      expect(result.recommendations?.some(r => r.includes('Start development server'))).toBe(true);
      expect(result.recommendations?.some(r => r.includes('React DevTools'))).toBe(true);
    });
  });
});