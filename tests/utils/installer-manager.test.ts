import { describe, test, expect, beforeEach, vi, afterEach } from 'vitest';
import {
  INSTALLER_APPROVAL_SCOPE,
  InstallerManager,
  InstallationTemplate,
} from '../../src/utils/installer-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';
import { spawn } from 'child_process';
import { parse as parseYaml } from 'yaml';

// Mock dependencies
vi.mock('fs/promises');
vi.mock('child_process');

describe('InstallerManager', () => {
  let installerManager: InstallerManager;
  let previousEnv: NodeJS.ProcessEnv;
  const testProjectRoot = '/test/project';
  const approvedContext = {
    dryRun: false,
    approval: {
      approved: true,
      scope: INSTALLER_APPROVAL_SCOPE,
    },
  } as const;

  beforeEach(() => {
    previousEnv = { ...process.env };
    process.env = {
      PATH: previousEnv['PATH'],
      HOME: previousEnv['HOME'],
    };
    vi.clearAllMocks();
    
    // Mock file system operations
    vi.mocked(fs.access).mockResolvedValue(undefined);
    vi.mocked(fs.mkdir).mockResolvedValue(undefined);
    vi.mocked(fs.writeFile).mockResolvedValue(undefined);
    vi.mocked(fs.readFile).mockResolvedValue('{"name":"test","version":"1.0.0"}');
    vi.mocked(fs.readdir).mockResolvedValue([]);

    installerManager = new InstallerManager(testProjectRoot);
  });

  afterEach(() => {
    process.env = previousEnv;
    vi.restoreAllMocks();
  });

  describe('Template Management', () => {
    test('should load default templates', () => {
      const templates = installerManager.getAvailableTemplates();
      
      expect(templates.length).toBeGreaterThan(0);
      expect(templates.find(t => t.id === 'typescript-node')).toBeDefined();
      expect(templates.find(t => t.id === 'react-vite')).toBeDefined();
      expect(templates.find(t => t.id === 'express-api')).toBeDefined();
    });

    test('should get template by ID', () => {
      const template = installerManager.getTemplate('typescript-node');
      
      expect(template).toBeDefined();
      expect(template?.id).toBe('typescript-node');
      expect(template?.name).toContain('TypeScript Node.js');
      expect(template?.language).toBe('typescript');
    });

    test('should get templates by category', () => {
      const webTemplates = installerManager.getTemplatesByCategory('web');
      const apiTemplates = installerManager.getTemplatesByCategory('api');
      
      expect(webTemplates.length).toBeGreaterThan(0);
      expect(apiTemplates.length).toBeGreaterThan(0);
      expect(webTemplates.every(t => t.category === 'web')).toBe(true);
      expect(apiTemplates.every(t => t.category === 'api')).toBe(true);
    });

    test('should return undefined for non-existent template', () => {
      const template = installerManager.getTemplate('non-existent');
      expect(template).toBeUndefined();
    });
  });

  describe('Package Manager Detection', () => {
    test('should detect pnpm from lock file', async () => {
      // Create separate mocks for fileExists method calls
      const mockFileExists = vi.fn()
        .mockResolvedValueOnce(true)  // pnpm-lock.yaml exists
        .mockResolvedValueOnce(false) // yarn.lock does not exist
        .mockResolvedValueOnce(false); // package-lock.json does not exist
      
      installerManager['fileExists'] = mockFileExists;

      const packageManager = await installerManager.detectPackageManager();
      expect(packageManager).toBe('pnpm');
    });

    test('should detect yarn from lock file', async () => {
      // Create separate mocks for fileExists method calls
      const mockFileExists = vi.fn()
        .mockResolvedValueOnce(false) // pnpm-lock.yaml does not exist
        .mockResolvedValueOnce(true)  // yarn.lock exists
        .mockResolvedValueOnce(false); // package-lock.json does not exist
      
      installerManager['fileExists'] = mockFileExists;

      const packageManager = await installerManager.detectPackageManager();
      expect(packageManager).toBe('yarn');
    });

    test('should detect npm from lock file', async () => {
      vi.mocked(fs.access)
        .mockRejectedValueOnce(new Error('not found')) // pnpm-lock.yaml
        .mockRejectedValueOnce(new Error('not found')) // yarn.lock
        .mockResolvedValueOnce(undefined); // package-lock.json

      const packageManager = await installerManager.detectPackageManager();
      expect(packageManager).toBe('npm');
    });

    test('should fall back to npm when no lock files found', async () => {
      vi.mocked(fs.access).mockRejectedValue(new Error('not found'));
      
      // Mock spawn to reject for pnpm and yarn version checks
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(1); // Exit with error
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      const packageManager = await installerManager.detectPackageManager();
      expect(packageManager).toBe('npm');
    });
  });

  describe('Template Installation', () => {
    test('should install template successfully', async () => {
      // Mock successful installation
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(0); // Exit successfully
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      const result = await installerManager.installTemplate('typescript-node', approvedContext);
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Successfully installed');
      // Don't check arrays in mocked environment - focus on success and basic functionality
      expect(result.errors.length).toBe(0);
    });

    test('should handle non-existent template', async () => {
      const result = await installerManager.installTemplate('non-existent');
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('Template non-existent not found');
      expect(result.errors).toContain('Template non-existent not found');
    });

    test('should handle installation failure', async () => {
      // Mock failed installation
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(1); // Exit with error
          if (event === 'error') callback(new Error('Installation failed'));
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      const result = await installerManager.installTemplate('typescript-node', approvedContext);
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('Installation failed');
    });

    test('should create package.json if not exists', async () => {
      vi.mocked(fs.readFile).mockRejectedValueOnce(new Error('File not found'));
      
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(0);
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      await installerManager.installTemplate('typescript-node', {
        ...approvedContext,
        projectName: 'test-project'
      });
      
      // Verify package.json was created
      expect(vi.mocked(fs.writeFile)).toHaveBeenCalledWith(
        path.join(testProjectRoot, 'package.json'),
        expect.stringContaining('"name": "test"')
      );
    });

    test('should default to dry-run without approval and avoid writes or package-manager spawn', async () => {
      const result = await installerManager.installTemplate('react-vite', {
        packageManager: 'pnpm',
      });

      expect(result.success).toBe(true);
      expect(result.dryRun).toBe(true);
      expect(result.message).toContain('Dry-run preview');
      const dependencyPlans =
        result.plannedChanges?.filter(change => change.type === 'dependency') ?? [];
      const devDependencyPlans =
        result.plannedChanges?.filter(change => change.type === 'devDependency') ?? [];
      expect(dependencyPlans).toHaveLength(1);
      expect(dependencyPlans[0]?.args).toEqual([
        'add',
        '--ignore-scripts',
        'react@^18.2.0',
        'react-dom@^18.2.0',
      ]);
      expect(devDependencyPlans).toHaveLength(1);
      expect(devDependencyPlans[0]?.args).toEqual([
        'add',
        '--ignore-scripts',
        '-D',
        'typescript@^5.0.0',
        '@types/react@^18.2.0',
        '@types/react-dom@^18.2.0',
        '@vitejs/plugin-react@^4.0.0',
        'vite@^5.0.0',
        'eslint@^8.0.0',
      ]);
      expect(vi.mocked(spawn)).not.toHaveBeenCalled();
      expect(vi.mocked(fs.writeFile)).not.toHaveBeenCalled();
      expect(vi.mocked(fs.mkdir)).not.toHaveBeenCalled();
    });

    test('should reject explicit apply without installer approval before writes or package-manager spawn', async () => {
      vi.mocked(fs.access).mockRejectedValue(new Error('not found'));

      const result = await installerManager.installTemplate('react-vite', {
        dryRun: false,
      });

      expect(result.success).toBe(false);
      expect(result.approvalRequired).toBe(true);
      expect(result.message).toContain(INSTALLER_APPROVAL_SCOPE);
      expect(result.plannedChanges?.length).toBeGreaterThan(0);
      expect(vi.mocked(spawn)).not.toHaveBeenCalled();
      expect(vi.mocked(fs.writeFile)).not.toHaveBeenCalled();
      expect(vi.mocked(fs.mkdir)).not.toHaveBeenCalled();
    });

    test('should force approved apply to dry-run in an untrusted checkout', async () => {
      const previous = process.env['AE_UNTRUSTED_CHECKOUT'];
      process.env['AE_UNTRUSTED_CHECKOUT'] = '1';
      vi.mocked(fs.access).mockRejectedValue(new Error('not found'));

      try {
        const result = await installerManager.installTemplate('react-vite', {
          ...approvedContext,
        });

        expect(result.success).toBe(true);
        expect(result.dryRun).toBe(true);
        expect(result.message).toContain('Dry-run preview');
        expect(result.plannedChanges?.length).toBeGreaterThan(0);
        expect(vi.mocked(spawn)).not.toHaveBeenCalled();
        expect(vi.mocked(fs.writeFile)).not.toHaveBeenCalled();
      } finally {
        if (previous === undefined) {
          delete process.env['AE_UNTRUSTED_CHECKOUT'];
        } else {
          process.env['AE_UNTRUSTED_CHECKOUT'] = previous;
        }
      }
    });

    test('should install dependencies with argv-safe spawn and lifecycle scripts suppressed by default', async () => {
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(0);
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      const result = await installerManager.installTemplate('react-vite', {
        ...approvedContext,
        packageManager: 'npm',
      });

      expect(result.success).toBe(true);
      expect(result.dryRun).toBe(false);
      expect(vi.mocked(spawn)).toHaveBeenNthCalledWith(
        1,
        'npm',
        ['install', '--ignore-scripts', 'react@^18.2.0', 'react-dom@^18.2.0'],
        expect.objectContaining({ shell: false, cwd: path.resolve(testProjectRoot) })
      );
      expect(vi.mocked(spawn)).toHaveBeenNthCalledWith(
        2,
        'npm',
        [
          'install',
          '--ignore-scripts',
          '--save-dev',
          'typescript@^5.0.0',
          '@types/react@^18.2.0',
          '@types/react-dom@^18.2.0',
          '@vitejs/plugin-react@^4.0.0',
          'vite@^5.0.0',
          'eslint@^8.0.0',
        ],
        expect.objectContaining({ shell: false, cwd: path.resolve(testProjectRoot) })
      );
    });

    test('should redact ambient secret variables from package-manager child environments', async () => {
      process.env['GITHUB_TOKEN'] = 'ghs-secret';
      process.env['NPM_TOKEN'] = 'npm-secret';
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(0);
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      const result = await installerManager.installTemplate('react-vite', {
        ...approvedContext,
        packageManager: 'npm',
      });

      expect(result.success).toBe(true);
      const spawnOptions = vi.mocked(spawn).mock.calls[0]?.[2] as { env?: NodeJS.ProcessEnv };
      expect(spawnOptions.env?.['GITHUB_TOKEN']).toBeUndefined();
      expect(spawnOptions.env?.['NPM_TOKEN']).toBeUndefined();
    });

    test('should block approved CI apply when ambient secrets are present', async () => {
      process.env['CI'] = 'true';
      process.env['GITHUB_TOKEN'] = 'ghs-secret';

      const result = await installerManager.installTemplate('react-vite', {
        ...approvedContext,
        packageManager: 'npm',
      });

      expect(result.success).toBe(false);
      expect(result.message).toContain('ambient secrets');
      expect(vi.mocked(spawn)).not.toHaveBeenCalled();
      expect(vi.mocked(fs.writeFile)).not.toHaveBeenCalled();
    });

    test('should validate template file paths before applying package or file writes', async () => {
      const unsafeTemplate: InstallationTemplate = {
        id: 'unsafe-path-template',
        name: 'Unsafe Path Template',
        description: 'Template with unsafe relative output',
        category: 'library',
        language: 'typescript',
        dependencies: [{ name: 'left-pad' }],
        scripts: { test: 'vitest' },
        files: [{ path: '../outside.ts', content: 'export {}' }],
        configurations: [],
      };
      installerManager['templates'].set(unsafeTemplate.id, unsafeTemplate);

      const result = await installerManager.installTemplate(unsafeTemplate.id, approvedContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Installation failed');
      expect(vi.mocked(spawn)).not.toHaveBeenCalled();
      expect(vi.mocked(fs.writeFile)).not.toHaveBeenCalled();
      expect(vi.mocked(fs.mkdir)).not.toHaveBeenCalled();
    });
  });

  describe('Template Suggestions', () => {
    test('should suggest templates based on existing package.json', async () => {
      const mockPackageJson = {
        dependencies: {
          react: '^18.0.0',
          express: '^4.18.0'
        }
      };
      vi.mocked(fs.readFile).mockResolvedValue(JSON.stringify(mockPackageJson));

      const { suggestions, reasoning } = await installerManager.suggestTemplates();
      
      expect(suggestions.length).toBeGreaterThan(0);
      expect(suggestions).toContain('react-vite');
      expect(suggestions).toContain('express-api');
      expect(reasoning).toContain('React dependencies detected');
      expect(reasoning).toContain('Express.js detected');
    });

    test('should suggest starter templates when no package.json exists', async () => {
      vi.mocked(fs.access).mockRejectedValue(new Error('File not found'));

      const { suggestions, reasoning } = await installerManager.suggestTemplates();
      
      expect(suggestions).toContain('typescript-node');
      expect(reasoning).toContain('No existing package.json found - suggesting starter templates');
    });

    test('should suggest templates based on file types', async () => {
      vi.mocked(fs.access).mockRejectedValue(new Error('No package.json'));
      vi.mocked(fs.readdir).mockResolvedValue([
        { name: 'main.py', isDirectory: () => false, isFile: () => true },
        { name: 'app.rs', isDirectory: () => false, isFile: () => true }
      ] as any);

      const { reasoning } = await installerManager.suggestTemplates();
      
      expect(reasoning).toContain('Python files detected');
      expect(reasoning).toContain('Rust files detected');
    });
  });

  describe('Custom Templates', () => {
    test('should create and store custom template', async () => {
      const customTemplate: InstallationTemplate = {
        id: 'custom-template',
        name: 'Custom Template',
        description: 'A custom template for testing',
        category: 'library',
        language: 'typescript',
        dependencies: [{ name: 'lodash' }],
        scripts: { test: 'jest' },
        files: [{ path: 'index.ts', content: 'export {}' }],
        configurations: []
      };

      await installerManager.createCustomTemplate(customTemplate);
      
      const retrievedTemplate = installerManager.getTemplate('custom-template');
      expect(retrievedTemplate).toEqual(customTemplate);
      
      // Verify template was saved to file
      expect(vi.mocked(fs.writeFile)).toHaveBeenCalledWith(
        expect.stringContaining('custom-templates.json'),
        expect.stringContaining('"custom-template"')
      );
    });
  });

  describe('Configuration Handling', () => {
    test('should handle JSON configurations', async () => {
      const template = installerManager.getTemplate('typescript-node');
      expect(template).toBeDefined();
      
      const jsonConfig = template!.configurations.find(c => c.format === 'json');
      expect(jsonConfig).toBeDefined();
      expect(jsonConfig!.file).toBe('tsconfig.json');
    });

    test('should handle TypeScript configurations', async () => {
      const template = installerManager.getTemplate('react-vite');
      expect(template).toBeDefined();
      
      const tsConfig = template!.configurations.find(c => c.format === 'ts');
      expect(tsConfig).toBeDefined();
      expect(tsConfig!.file).toBe('vite.config.ts');
    });

    test('should serialize YAML configurations without JSON fallback warning', async () => {
      const template: InstallationTemplate = {
        id: 'yaml-config-template',
        name: 'YAML Config Template',
        description: 'Template for YAML configuration serialization test',
        category: 'library',
        language: 'typescript',
        dependencies: [],
        scripts: {},
        files: [],
        configurations: [
          {
            file: 'config/app.yaml',
            format: 'yaml',
            content: {
              app: { name: 'ae-framework', mode: 'test' },
              features: ['installer', 'yaml'],
            },
          },
        ],
      };

      const result = {
        success: true,
        message: '',
        installedDependencies: [],
        createdFiles: [],
        configuredFiles: [],
        executedSteps: [],
        warnings: [],
        errors: [],
        duration: 0,
      };

      await installerManager['applyConfigurations'](template, {
        projectRoot: testProjectRoot,
        projectName: 'test-project',
        packageManager: 'pnpm',
      }, result);

      const yamlWriteCall = vi.mocked(fs.writeFile).mock.calls.find(
        ([filePath]) => filePath === path.join(testProjectRoot, 'config/app.yaml')
      );
      expect(yamlWriteCall).toBeDefined();

      const writtenContent = yamlWriteCall?.[1];
      expect(typeof writtenContent).toBe('string');
      expect(parseYaml(String(writtenContent))).toEqual({
        app: { name: 'ae-framework', mode: 'test' },
        features: ['installer', 'yaml'],
      });
      expect(result.warnings).toEqual([]);
      expect(result.configuredFiles).toContain('config/app.yaml');
    });

    test('should serialize ENV and INI configurations without unsupported warning', async () => {
      const template: InstallationTemplate = {
        id: 'env-ini-config-template',
        name: 'ENV/INI Config Template',
        description: 'Template for ENV and INI serialization test',
        category: 'library',
        language: 'typescript',
        dependencies: [],
        scripts: {},
        files: [],
        configurations: [
          {
            file: '.env',
            format: 'env',
            content: {
              appName: 'ae-framework',
              apiUrl: 'https://example.com',
              retryCount: 3,
              debugMode: true,
            },
          },
          {
            file: 'config/app.ini',
            format: 'ini',
            content: {
              mode: 'test',
              retries: 5,
              database: {
                host: 'localhost',
                port: 5432,
              },
            },
          },
        ],
      };

      const result = {
        success: true,
        message: '',
        installedDependencies: [],
        createdFiles: [],
        configuredFiles: [],
        executedSteps: [],
        warnings: [],
        errors: [],
        duration: 0,
      };

      await installerManager['applyConfigurations'](template, {
        projectRoot: testProjectRoot,
        projectName: 'test-project',
        packageManager: 'pnpm',
      }, result);

      const envWriteCall = vi.mocked(fs.writeFile).mock.calls.find(
        ([filePath]) => filePath === path.join(testProjectRoot, '.env')
      );
      expect(envWriteCall).toBeDefined();
      expect(String(envWriteCall?.[1])).toContain('APPNAME=ae-framework');
      expect(String(envWriteCall?.[1])).toContain('APIURL=https://example.com');
      expect(String(envWriteCall?.[1])).toContain('RETRYCOUNT=3');
      expect(String(envWriteCall?.[1])).toContain('DEBUGMODE=true');

      const iniWriteCall = vi.mocked(fs.writeFile).mock.calls.find(
        ([filePath]) => filePath === path.join(testProjectRoot, 'config/app.ini')
      );
      expect(iniWriteCall).toBeDefined();
      expect(String(iniWriteCall?.[1])).toContain('mode=test');
      expect(String(iniWriteCall?.[1])).toContain('retries=5');
      expect(String(iniWriteCall?.[1])).toContain('[database]');
      expect(String(iniWriteCall?.[1])).toContain('host=localhost');
      expect(String(iniWriteCall?.[1])).toContain('port=5432');

      expect(result.warnings).toEqual([]);
      expect(result.configuredFiles).toEqual(expect.arrayContaining(['.env', 'config/app.ini']));
    });

    test('should merge JSON configurations when merge policy is enabled', async () => {
      const template: InstallationTemplate = {
        id: 'json-merge-config-template',
        name: 'JSON Merge Config Template',
        description: 'Template for JSON configuration merge test',
        category: 'library',
        language: 'typescript',
        dependencies: [],
        scripts: {},
        files: [],
        configurations: [
          {
            file: 'tsconfig.json',
            format: 'json',
            merge: true,
            content: {
              compilerOptions: {
                target: 'ES2022',
                strict: true,
              },
            },
          },
        ],
      };

      vi.mocked(fs.readFile).mockResolvedValueOnce(JSON.stringify({
        compilerOptions: {
          module: 'commonjs',
          strict: false,
        },
        include: ['src/**/*'],
      }));

      const result = {
        success: true,
        message: '',
        installedDependencies: [],
        createdFiles: [],
        configuredFiles: [],
        executedSteps: [],
        warnings: [],
        errors: [],
        duration: 0,
      };

      await installerManager['applyConfigurations'](template, {
        projectRoot: testProjectRoot,
        projectName: 'test-project',
        packageManager: 'pnpm',
      }, result);

      const writeCall = vi.mocked(fs.writeFile).mock.calls.find(
        ([filePath]) => filePath === path.join(testProjectRoot, 'tsconfig.json')
      );
      expect(writeCall).toBeDefined();
      const writtenConfig = JSON.parse(String(writeCall?.[1]));
      expect(writtenConfig).toEqual({
        compilerOptions: {
          module: 'commonjs',
          strict: true,
          target: 'ES2022',
        },
        include: ['src/**/*'],
      });
      expect(result.configuredFiles).toContain('tsconfig.json');
    });
  });

  describe('File Operations', () => {
    test('should create template files with correct content', async () => {
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(0);
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      await installerManager.installTemplate('typescript-node', approvedContext);
      
      // Verify package.json was created (this is the first file created)
      expect(vi.mocked(fs.writeFile)).toHaveBeenCalledWith(
        path.join(testProjectRoot, 'package.json'),
        expect.stringContaining('"name":')
      );
      
      expect(vi.mocked(fs.writeFile)).toHaveBeenCalledWith(
        path.join(testProjectRoot, 'tsconfig.json'),
        expect.stringContaining('compilerOptions')
      );
    });

    test('should skip existing files when overwrite is false', async () => {
      vi.mocked(fs.access).mockResolvedValue(undefined); // File exists
      
      const mockProcess = {
        stdout: { on: vi.fn() },
        stderr: { on: vi.fn() },
        on: vi.fn().mockImplementation((event, callback) => {
          if (event === 'close') callback(0);
        })
      };
      vi.mocked(spawn).mockReturnValue(mockProcess as any);

      const result = await installerManager.installTemplate('typescript-node', approvedContext);
      
      expect(result.warnings.some(w => w.includes('already exists, skipping'))).toBe(true);
    });
  });
});
