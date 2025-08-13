/**
 * Integrated Installer Manager for ae-framework
 * Manages project setup, dependency installation, and configuration
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { spawn } from 'child_process';

export interface InstallationTemplate {
  id: string;
  name: string;
  description: string;
  category: 'web' | 'api' | 'cli' | 'library' | 'fullstack' | 'mobile';
  framework?: string;
  language: 'typescript' | 'javascript' | 'python' | 'rust' | 'go' | 'java';
  dependencies: Dependency[];
  devDependencies?: Dependency[];
  scripts: Record<string, string>;
  files: TemplateFile[];
  configurations: Configuration[];
  postInstallSteps?: InstallStep[];
}

export interface Dependency {
  name: string;
  version?: string;
  optional?: boolean;
  condition?: string; // e.g., "node >=16"
  alternatives?: string[]; // Alternative packages
}

export interface TemplateFile {
  path: string;
  content: string | (() => string);
  overwrite?: boolean;
  condition?: string;
}

export interface Configuration {
  file: string;
  format: 'json' | 'yaml' | 'env' | 'ini' | 'js' | 'ts';
  content: Record<string, any> | string;
  merge?: boolean; // Merge with existing file
}

export interface InstallStep {
  type: 'command' | 'file' | 'config' | 'message';
  description: string;
  action: string | (() => Promise<void>);
  condition?: string;
  required?: boolean;
}

export interface InstallationContext {
  projectRoot: string;
  projectName: string;
  packageManager: 'npm' | 'yarn' | 'pnpm';
  nodeVersion?: string;
  existingPackageJson?: any;
  userPreferences?: Record<string, any>;
}

export interface InstallationResult {
  success: boolean;
  message: string;
  installedDependencies: string[];
  createdFiles: string[];
  configuredFiles: string[];
  executedSteps: string[];
  warnings: string[];
  errors: string[];
  duration: number;
}

export class InstallerManager {
  private templates: Map<string, InstallationTemplate> = new Map();
  private projectRoot: string;

  constructor(projectRoot: string) {
    this.projectRoot = projectRoot;
    this.loadDefaultTemplates();
  }

  /**
   * Get available installation templates
   */
  getAvailableTemplates(): InstallationTemplate[] {
    return Array.from(this.templates.values());
  }

  /**
   * Get templates by category
   */
  getTemplatesByCategory(category: InstallationTemplate['category']): InstallationTemplate[] {
    return this.getAvailableTemplates().filter(template => template.category === category);
  }

  /**
   * Get template by ID
   */
  getTemplate(id: string): InstallationTemplate | undefined {
    return this.templates.get(id);
  }

  /**
   * Install a template
   */
  async installTemplate(
    templateId: string, 
    context: Partial<InstallationContext> = {}
  ): Promise<InstallationResult> {
    const startTime = Date.now();
    const template = this.templates.get(templateId);
    
    if (!template) {
      return {
        success: false,
        message: `Template ${templateId} not found`,
        installedDependencies: [],
        createdFiles: [],
        configuredFiles: [],
        executedSteps: [],
        warnings: [],
        errors: [`Template ${templateId} not found`],
        duration: Date.now() - startTime
      };
    }

    const installContext = await this.prepareContext(context);
    const result: InstallationResult = {
      success: true,
      message: '',
      installedDependencies: [],
      createdFiles: [],
      configuredFiles: [],
      executedSteps: [],
      warnings: [],
      errors: [],
      duration: 0
    };

    try {
      // Install dependencies
      await this.installDependencies(template, installContext, result);
      
      // Create template files
      await this.createTemplateFiles(template, installContext, result);
      
      // Apply configurations
      await this.applyConfigurations(template, installContext, result);
      
      // Execute post-install steps
      await this.executePostInstallSteps(template, installContext, result);
      
      result.message = `Successfully installed ${template.name}`;
      
    } catch (error: any) {
      result.success = false;
      result.message = `Installation failed: ${error.message}`;
      result.errors.push(error.message);
    }

    result.duration = Date.now() - startTime;
    return result;
  }

  /**
   * Detect project type and suggest templates
   */
  async suggestTemplates(): Promise<{ suggestions: string[]; reasoning: string[] }> {
    const suggestions: string[] = [];
    const reasoning: string[] = [];

    try {
      // Check existing package.json
      const packageJsonPath = path.join(this.projectRoot, 'package.json');
      const packageJsonExists = await this.fileExists(packageJsonPath);
      
      if (packageJsonExists) {
        const packageJson = JSON.parse(await fs.readFile(packageJsonPath, 'utf-8'));
        
        // Analyze existing dependencies
        const allDeps = {
          ...packageJson.dependencies,
          ...packageJson.devDependencies
        };

        if (allDeps.react) {
          suggestions.push('react-typescript', 'react-vite');
          reasoning.push('React dependencies detected');
        }
        
        if (allDeps.next) {
          suggestions.push('nextjs-app');
          reasoning.push('Next.js detected');
        }
        
        if (allDeps.express) {
          suggestions.push('express-api', 'node-backend');
          reasoning.push('Express.js detected');
        }
        
        if (allDeps.vue) {
          suggestions.push('vue-typescript');
          reasoning.push('Vue.js detected');
        }
      } else {
        // No package.json, suggest starter templates
        suggestions.push('typescript-node', 'vanilla-typescript', 'node-cli');
        reasoning.push('No existing package.json found - suggesting starter templates');
      }

      // Check for specific file types
      const files = await this.getProjectFiles();
      
      if (files.some(f => f.endsWith('.py'))) {
        suggestions.push('python-fastapi', 'python-flask');
        reasoning.push('Python files detected');
      }
      
      if (files.some(f => f.endsWith('.rs'))) {
        suggestions.push('rust-cli', 'rust-web');
        reasoning.push('Rust files detected');
      }

    } catch (error) {
      reasoning.push('Failed to analyze project structure');
    }

    return { suggestions, reasoning };
  }

  /**
   * Create a custom template
   */
  async createCustomTemplate(template: InstallationTemplate): Promise<void> {
    this.templates.set(template.id, template);
    
    // Save to custom templates file
    await this.saveCustomTemplate(template);
  }

  /**
   * Update package manager detection
   */
  async detectPackageManager(): Promise<'npm' | 'yarn' | 'pnpm'> {
    const lockFiles = [
      { file: 'pnpm-lock.yaml', manager: 'pnpm' as const },
      { file: 'yarn.lock', manager: 'yarn' as const },
      { file: 'package-lock.json', manager: 'npm' as const }
    ];

    for (const { file, manager } of lockFiles) {
      const exists = await this.fileExists(path.join(this.projectRoot, file));
      if (exists) {
        return manager;
      }
    }

    // Check if package managers are globally available
    try {
      await this.runCommand('pnpm --version', { silent: true });
      return 'pnpm';
    } catch {}

    try {
      await this.runCommand('yarn --version', { silent: true });
      return 'yarn';
    } catch {}

    return 'npm'; // Default fallback
  }

  // Private methods

  private loadDefaultTemplates(): void {
    const templates: InstallationTemplate[] = [
      {
        id: 'typescript-node',
        name: 'TypeScript Node.js Project',
        description: 'Basic TypeScript Node.js project with essential tooling',
        category: 'api',
        language: 'typescript',
        dependencies: [],
        devDependencies: [
          { name: 'typescript', version: '^5.0.0' },
          { name: '@types/node', version: '^20.0.0' },
          { name: 'tsx', version: '^4.0.0' },
          { name: 'eslint', version: '^8.0.0' },
          { name: '@typescript-eslint/eslint-plugin', version: '^6.0.0' },
          { name: '@typescript-eslint/parser', version: '^6.0.0' }
        ],
        scripts: {
          'dev': 'tsx src/index.ts',
          'build': 'tsc',
          'start': 'node dist/index.js',
          'lint': 'eslint src/**/*.ts',
          'type-check': 'tsc --noEmit'
        },
        files: [
          {
            path: 'src/index.ts',
            content: `console.log('Hello, TypeScript Node.js!');\n\nexport {};\n`
          },
          {
            path: '.gitignore',
            content: `node_modules/\ndist/\n.env\n*.log\n.DS_Store\n`
          }
        ],
        configurations: [
          {
            file: 'tsconfig.json',
            format: 'json',
            content: {
              compilerOptions: {
                target: 'ES2022',
                module: 'commonjs',
                lib: ['ES2022'],
                outDir: './dist',
                rootDir: './src',
                strict: true,
                esModuleInterop: true,
                skipLibCheck: true,
                forceConsistentCasingInFileNames: true,
                resolveJsonModule: true,
                moduleResolution: 'node'
              },
              include: ['src/**/*'],
              exclude: ['node_modules', 'dist']
            }
          }
        ]
      },
      {
        id: 'react-vite',
        name: 'React + Vite + TypeScript',
        description: 'Modern React development setup with Vite and TypeScript',
        category: 'web',
        framework: 'react',
        language: 'typescript',
        dependencies: [
          { name: 'react', version: '^18.2.0' },
          { name: 'react-dom', version: '^18.2.0' }
        ],
        devDependencies: [
          { name: 'typescript', version: '^5.0.0' },
          { name: '@types/react', version: '^18.2.0' },
          { name: '@types/react-dom', version: '^18.2.0' },
          { name: '@vitejs/plugin-react', version: '^4.0.0' },
          { name: 'vite', version: '^5.0.0' },
          { name: 'eslint', version: '^8.0.0' }
        ],
        scripts: {
          'dev': 'vite',
          'build': 'tsc && vite build',
          'preview': 'vite preview',
          'lint': 'eslint src --ext ts,tsx'
        },
        files: [
          {
            path: 'src/App.tsx',
            content: `import { useState } from 'react'\n\nfunction App() {\n  const [count, setCount] = useState(0)\n\n  return (\n    <div>\n      <h1>Hello React + Vite!</h1>\n      <button onClick={() => setCount(count + 1)}>\n        Count: {count}\n      </button>\n    </div>\n  )\n}\n\nexport default App\n`
          },
          {
            path: 'src/main.tsx',
            content: `import React from 'react'\nimport ReactDOM from 'react-dom/client'\nimport App from './App'\n\nReactDOM.createRoot(document.getElementById('root')!).render(\n  <React.StrictMode>\n    <App />\n  </React.StrictMode>,\n)\n`
          },
          {
            path: 'index.html',
            content: `<!DOCTYPE html>\n<html lang="en">\n  <head>\n    <meta charset="UTF-8" />\n    <meta name="viewport" content="width=device-width, initial-scale=1.0" />\n    <title>React + Vite App</title>\n  </head>\n  <body>\n    <div id="root"></div>\n    <script type="module" src="/src/main.tsx"></script>\n  </body>\n</html>\n`
          }
        ],
        configurations: [
          {
            file: 'vite.config.ts',
            format: 'ts',
            content: `import { defineConfig } from 'vite'\nimport react from '@vitejs/plugin-react'\n\nexport default defineConfig({\n  plugins: [react()],\n})\n`
          }
        ]
      },
      {
        id: 'express-api',
        name: 'Express.js API',
        description: 'RESTful API with Express.js, TypeScript, and common middleware',
        category: 'api',
        framework: 'express',
        language: 'typescript',
        dependencies: [
          { name: 'express', version: '^4.18.0' },
          { name: 'cors', version: '^2.8.5' },
          { name: 'helmet', version: '^7.0.0' },
          { name: 'dotenv', version: '^16.0.0' }
        ],
        devDependencies: [
          { name: 'typescript', version: '^5.0.0' },
          { name: '@types/node', version: '^20.0.0' },
          { name: '@types/express', version: '^4.17.0' },
          { name: '@types/cors', version: '^2.8.0' },
          { name: 'tsx', version: '^4.0.0' },
          { name: 'nodemon', version: '^3.0.0' }
        ],
        scripts: {
          'dev': 'nodemon src/server.ts',
          'build': 'tsc',
          'start': 'node dist/server.js',
          'lint': 'eslint src/**/*.ts'
        },
        files: [
          {
            path: 'src/server.ts',
            content: `import express from 'express';\nimport cors from 'cors';\nimport helmet from 'helmet';\nimport dotenv from 'dotenv';\n\ndotenv.config();\n\nconst app = express();\nconst PORT = process.env.PORT || 3000;\n\n// Middleware\napp.use(helmet());\napp.use(cors());\napp.use(express.json());\n\n// Routes\napp.get('/api/health', (req, res) => {\n  res.json({ status: 'OK', timestamp: new Date().toISOString() });\n});\n\napp.get('/api/hello', (req, res) => {\n  res.json({ message: 'Hello, API!' });\n});\n\napp.listen(PORT, () => {\n  console.log(\`Server running on port \${PORT}\`);\n});\n`
          },
          {
            path: '.env.example',
            content: `PORT=3000\nNODE_ENV=development\n`
          }
        ],
        configurations: []
      }
    ];

    for (const template of templates) {
      this.templates.set(template.id, template);
    }
  }

  private async prepareContext(context: Partial<InstallationContext>): Promise<InstallationContext> {
    const packageManager = context.packageManager || await this.detectPackageManager();
    const projectName = context.projectName || path.basename(this.projectRoot);
    
    let existingPackageJson;
    try {
      const packageJsonContent = await fs.readFile(
        path.join(this.projectRoot, 'package.json'),
        'utf-8'
      );
      existingPackageJson = JSON.parse(packageJsonContent);
    } catch {
      // No existing package.json
    }

    return {
      projectRoot: this.projectRoot,
      projectName,
      packageManager,
      existingPackageJson,
      ...context
    };
  }

  private async installDependencies(
    template: InstallationTemplate, 
    context: InstallationContext, 
    result: InstallationResult
  ): Promise<void> {
    // Ensure package.json exists
    await this.ensurePackageJson(context);

    // Install regular dependencies
    if (template.dependencies.length > 0) {
      const depNames = template.dependencies.map(d => d.version ? `${d.name}@${d.version}` : d.name);
      await this.runPackageManagerCommand(context.packageManager, 'install', depNames);
      result.installedDependencies.push(...depNames);
    }

    // Install dev dependencies
    if (template.devDependencies && template.devDependencies.length > 0) {
      const devDepNames = template.devDependencies.map(d => d.version ? `${d.name}@${d.version}` : d.name);
      await this.runPackageManagerCommand(context.packageManager, 'install', devDepNames, true);
      result.installedDependencies.push(...devDepNames.map(d => `${d} (dev)`));
    }

    // Update scripts
    await this.updatePackageJsonScripts(template.scripts, context);
  }

  private async createTemplateFiles(
    template: InstallationTemplate, 
    context: InstallationContext, 
    result: InstallationResult
  ): Promise<void> {
    for (const file of template.files) {
      const filePath = path.join(context.projectRoot, file.path);
      const dir = path.dirname(filePath);

      // Ensure directory exists
      await fs.mkdir(dir, { recursive: true });

      // Check if file exists and overwrite policy
      const exists = await this.fileExists(filePath);
      if (exists && !file.overwrite) {
        result.warnings.push(`File ${file.path} already exists, skipping`);
        continue;
      }

      // Generate content
      const content = typeof file.content === 'function' ? file.content() : file.content;
      
      await fs.writeFile(filePath, content);
      result.createdFiles.push(file.path);
    }
  }

  private async applyConfigurations(
    template: InstallationTemplate, 
    context: InstallationContext, 
    result: InstallationResult
  ): Promise<void> {
    for (const config of template.configurations) {
      const configPath = path.join(context.projectRoot, config.file);
      
      let configContent: string;
      if (typeof config.content === 'string') {
        configContent = config.content;
      } else {
        switch (config.format) {
          case 'json':
            configContent = JSON.stringify(config.content, null, 2);
            break;
          case 'yaml':
            // TODO: Implement proper YAML support by adding yaml library dependency
            configContent = JSON.stringify(config.content, null, 2);
            result.warnings.push('YAML format not implemented, falling back to JSON');
            break;
          case 'js':
          case 'ts':
            configContent = typeof config.content === 'string' 
              ? config.content 
              : `export default ${JSON.stringify(config.content, null, 2)};`;
            break;
          default:
            configContent = JSON.stringify(config.content, null, 2);
        }
      }

      const dir = path.dirname(configPath);
      await fs.mkdir(dir, { recursive: true });
      
      await fs.writeFile(configPath, configContent);
      result.configuredFiles.push(config.file);
    }
  }

  private async executePostInstallSteps(
    template: InstallationTemplate, 
    context: InstallationContext, 
    result: InstallationResult
  ): Promise<void> {
    if (!template.postInstallSteps) return;

    for (const step of template.postInstallSteps) {
      try {
        if (typeof step.action === 'function') {
          await step.action();
        } else {
          await this.runCommand(step.action);
        }
        result.executedSteps.push(step.description);
      } catch (error: any) {
        const message = `Failed to execute step "${step.description}": ${error.message}`;
        if (step.required) {
          throw new Error(message);
        } else {
          result.warnings.push(message);
        }
      }
    }
  }

  private async ensurePackageJson(context: InstallationContext): Promise<void> {
    const packageJsonPath = path.join(context.projectRoot, 'package.json');
    const exists = await this.fileExists(packageJsonPath);
    
    if (!exists) {
      const packageJson = {
        name: context.projectName,
        version: '1.0.0',
        description: '',
        main: 'index.js',
        scripts: {},
        keywords: [],
        author: '',
        license: 'MIT'
      };
      
      await fs.writeFile(packageJsonPath, JSON.stringify(packageJson, null, 2));
    }
  }

  private async updatePackageJsonScripts(scripts: Record<string, string>, context: InstallationContext): Promise<void> {
    const packageJsonPath = path.join(context.projectRoot, 'package.json');
    const packageJsonContent = await fs.readFile(packageJsonPath, 'utf-8');
    const packageJson = JSON.parse(packageJsonContent);
    
    packageJson.scripts = { ...packageJson.scripts, ...scripts };
    
    await fs.writeFile(packageJsonPath, JSON.stringify(packageJson, null, 2));
  }

  private async runPackageManagerCommand(
    packageManager: string, 
    command: string, 
    packages: string[], 
    dev: boolean = false
  ): Promise<void> {
    let cmd: string;
    
    switch (packageManager) {
      case 'yarn':
        cmd = dev ? `yarn add -D ${packages.join(' ')}` : `yarn add ${packages.join(' ')}`;
        break;
      case 'pnpm':
        cmd = dev ? `pnpm add -D ${packages.join(' ')}` : `pnpm add ${packages.join(' ')}`;
        break;
      default: // npm
        cmd = dev ? `npm install --save-dev ${packages.join(' ')}` : `npm install ${packages.join(' ')}`;
    }
    
    await this.runCommand(cmd);
  }

  private async runCommand(command: string, options: { silent?: boolean } = {}): Promise<string> {
    return new Promise((resolve, reject) => {
      const [cmd, ...args] = command.split(' ');
      const process = spawn(cmd, args, { 
        cwd: this.projectRoot,
        stdio: options.silent ? 'pipe' : 'inherit'
      });
      
      let output = '';
      
      if (options.silent) {
        process.stdout?.on('data', (data) => {
          output += data.toString();
        });
        
        process.stderr?.on('data', (data) => {
          output += data.toString();
        });
      }
      
      process.on('close', (code) => {
        if (code === 0) {
          resolve(output);
        } else {
          reject(new Error(`Command failed with exit code ${code}: ${command}`));
        }
      });
      
      process.on('error', reject);
    });
  }

  private async fileExists(filePath: string): Promise<boolean> {
    try {
      await fs.access(filePath);
      return true;
    } catch {
      return false;
    }
  }

  private async getProjectFiles(): Promise<string[]> {
    const files: string[] = [];
    
    try {
      const scanDir = async (dir: string): Promise<void> => {
        const entries = await fs.readdir(dir, { withFileTypes: true });
        
        for (const entry of entries) {
          const fullPath = path.join(dir, entry.name);
          
          if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
            await scanDir(fullPath);
          } else if (entry.isFile()) {
            files.push(path.relative(this.projectRoot, fullPath));
          }
        }
      };
      
      await scanDir(this.projectRoot);
    } catch (error) {
      // Error scanning directory
    }
    
    return files;
  }

  private async saveCustomTemplate(template: InstallationTemplate): Promise<void> {
    const customTemplatesPath = path.join(this.projectRoot, '.ae-framework', 'custom-templates.json');
    
    let customTemplates: InstallationTemplate[] = [];
    
    try {
      const content = await fs.readFile(customTemplatesPath, 'utf-8');
      customTemplates = JSON.parse(content);
    } catch {
      // File doesn't exist yet
    }
    
    // Update or add template
    const index = customTemplates.findIndex(t => t.id === template.id);
    if (index >= 0) {
      customTemplates[index] = template;
    } else {
      customTemplates.push(template);
    }
    
    const dir = path.dirname(customTemplatesPath);
    await fs.mkdir(dir, { recursive: true });
    await fs.writeFile(customTemplatesPath, JSON.stringify(customTemplates, null, 2));
  }
}