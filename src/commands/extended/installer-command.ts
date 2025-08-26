/**
 * Installer Command for ae-framework
 * Provides project template installation and setup functionality
 */

import { BaseExtendedCommand, ExtendedCommandResult, ExtendedCommandConfig } from './base-command.js';
import { InstallerManager, InstallationTemplate, InstallationResult } from '../../utils/installer-manager.js';
import { ContextManager } from '../../utils/context-manager.js';
import { TokenOptimizer } from '../../utils/token-optimizer.js';
import type * as fs from 'fs/promises';
import * as path from 'path';

export interface InstallerCommandResult extends ExtendedCommandResult {
  installedTemplate?: string;
  installedDependencies?: string[];
  createdFiles?: string[];
  suggestions?: string[];
  recommendations?: string[];
  availableTemplates?: InstallationTemplate[];
}

export class InstallerCommand extends BaseExtendedCommand {
  public readonly name = '/ae:installer';
  public readonly description = 'Install project templates and manage dependencies';
  public readonly category = 'utility' as const;
  public readonly usage = '/ae:installer <template-id> | list | suggest | templates';
  public readonly aliases = ['/installer', '/install', '/a:installer'];

  private installerManager?: InstallerManager;
  private contextManager?: ContextManager;
  private tokenOptimizer?: TokenOptimizer;

  constructor(config?: ExtendedCommandConfig) {
    super(config);
  }

  private async getInstallerManager(projectRoot: string): Promise<InstallerManager> {
    if (!this.installerManager) {
      this.installerManager = new InstallerManager(projectRoot);
    }
    return this.installerManager;
  }

  private async getContextManager(projectRoot: string): Promise<ContextManager> {
    if (!this.contextManager) {
      this.contextManager = new ContextManager(projectRoot);
    }
    return this.contextManager;
  }

  private getTokenOptimizer(): TokenOptimizer {
    if (!this.tokenOptimizer) {
      this.tokenOptimizer = new TokenOptimizer();
    }
    return this.tokenOptimizer;
  }

  async handler(args: string[], context: any): Promise<InstallerCommandResult> {
    const startTime = Date.now();
    const projectRoot = context?.projectRoot || process.cwd();

    try {
      const installerManager = await this.getInstallerManager(projectRoot);
      const contextManager = await this.getContextManager(projectRoot);
      const tokenOptimizer = this.getTokenOptimizer();

      // Parse arguments
      const action = args[0]?.toLowerCase();

      if (!action) {
        return this.createErrorResult('No action specified. Use: install <template>, list, suggest, or templates');
      }

      switch (action) {
        case 'list':
        case 'templates':
          return await this.handleListTemplates(installerManager);

        case 'suggest':
          return await this.handleSuggestTemplates(installerManager);

        case 'help':
          return this.handleHelp();

        default:
          // Treat as template installation
          return await this.handleInstallTemplate(action, args.slice(1), installerManager, contextManager, tokenOptimizer, projectRoot);
      }

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Installer command failed: ${error.message}`);
    } finally {
      this.recordMetric('execution_time', Date.now() - startTime);
    }
  }

  private async handleListTemplates(installerManager: InstallerManager): Promise<InstallerCommandResult> {
    try {
      const templates = installerManager.getAvailableTemplates();
      
      let message = 'Available Templates:\n\n';
      
      const categories = [...new Set(templates.map(t => t.category))];
      for (const category of categories) {
        const categoryTemplates = templates.filter(t => t.category === category);
        message += `${category.toUpperCase()}:\n`;
        
        for (const template of categoryTemplates) {
          message += `  • ${template.id} - ${template.name}\n`;
          message += `    ${template.description}\n`;
          message += `    Language: ${template.language}`;
          if (template.framework) {
            message += `, Framework: ${template.framework}`;
          }
          message += '\n\n';
        }
      }

      message += 'Usage: /ae:installer <template-id> to install a template\n';
      message += 'Use /ae:installer suggest for project-specific recommendations';

      this.recordMetric('success');
      return {
        success: true,
        message,
        availableTemplates: templates,
        evidence: [`Found ${templates.length} available templates`],
        recommendations: ['Use /ae:installer suggest for personalized recommendations']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to list templates: ${error.message}`);
    }
  }

  private async handleSuggestTemplates(installerManager: InstallerManager): Promise<InstallerCommandResult> {
    try {
      const { suggestions, reasoning } = await installerManager.suggestTemplates();
      
      let message = 'Template Suggestions:\n\n';
      
      if (suggestions.length > 0) {
        message += 'Recommended templates based on your project:\n\n';
        
        for (let i = 0; i < suggestions.length; i++) {
          const templateId = suggestions[i];
          if (!templateId) continue;
          const template = installerManager.getTemplate(templateId);
          const reason = reasoning[i];
          
          message += `${i + 1}. ${templateId}`;
          if (template) {
            message += ` - ${template.name}\n`;
            message += `   ${template.description}\n`;
          } else {
            message += '\n';
          }
          message += `   Reason: ${reason}\n\n`;
        }
        
        message += `Use /ae:installer <template-id> to install any of these templates`;
      } else {
        message += 'No specific suggestions for this project.\n';
        message += 'Use /ae:installer list to see all available templates';
      }

      this.recordMetric('success');
      return {
        success: true,
        message,
        suggestions,
        evidence: reasoning,
        recommendations: suggestions.length > 0 ? 
          [`Consider installing: ${suggestions[0]}`] : 
          ['Review available templates with /ae:installer list']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to suggest templates: ${error.message}`);
    }
  }

  private async handleInstallTemplate(
    templateId: string, 
    additionalArgs: string[], 
    installerManager: InstallerManager, 
    contextManager: ContextManager, 
    tokenOptimizer: TokenOptimizer,
    projectRoot: string
  ): Promise<InstallerCommandResult> {
    try {
      // Check if template exists
      const template = installerManager.getTemplate(templateId);
      if (!template) {
        const suggestions = await installerManager.suggestTemplates();
        const availableTemplates = installerManager.getAvailableTemplates();
        
        let errorMessage = `Template '${templateId}' not found.\n\n`;
        errorMessage += 'Available templates:\n';
        availableTemplates.forEach(t => {
          errorMessage += `  • ${t.id} - ${t.name}\n`;
        });
        
        if (suggestions.suggestions.length > 0) {
          errorMessage += '\nSuggested for your project:\n';
          suggestions.suggestions.forEach(s => {
            errorMessage += `  • ${s}\n`;
          });
        }

        this.recordMetric('template_not_found');
        return this.createErrorResult(errorMessage);
      }

      // Parse additional options from args
      const installationContext = this.parseInstallationOptions(additionalArgs, projectRoot);

      // Install the template
      const result: InstallationResult = await installerManager.installTemplate(templateId, installationContext);

      if (!result.success) {
        this.recordMetric('installation_failed');
        let errorMessage = `Failed to install template '${templateId}': ${result.message}\n`;
        
        if (result.errors.length > 0) {
          errorMessage += '\nErrors:\n';
          result.errors.forEach(error => {
            errorMessage += `  • ${error}\n`;
          });
        }

        if (result.warnings.length > 0) {
          errorMessage += '\nWarnings:\n';
          result.warnings.forEach(warning => {
            errorMessage += `  • ${warning}\n`;
          });
        }

        return this.createErrorResult(errorMessage);
      }

      // Build success message
      let message = `Successfully installed '${template.name}' template!\n\n`;
      
      if (result.installedDependencies.length > 0) {
        message += `Installed dependencies:\n`;
        result.installedDependencies.forEach(dep => {
          message += `  • ${dep}\n`;
        });
        message += '\n';
      }

      if (result.createdFiles.length > 0) {
        message += `Created files:\n`;
        result.createdFiles.forEach(file => {
          message += `  • ${file}\n`;
        });
        message += '\n';
      }

      if (result.configuredFiles.length > 0) {
        message += `Configured files:\n`;
        result.configuredFiles.forEach(file => {
          message += `  • ${file}\n`;
        });
        message += '\n';
      }

      if (result.executedSteps.length > 0) {
        message += `Executed setup steps:\n`;
        result.executedSteps.forEach(step => {
          message += `  • ${step}\n`;
        });
        message += '\n';
      }

      if (result.warnings.length > 0) {
        message += `Warnings:\n`;
        result.warnings.forEach(warning => {
          message += `  • ${warning}\n`;
        });
        message += '\n';
      }

      message += `Installation completed in ${result.duration}ms`;

      // Update project context
      contextManager.addToMemory(`template_install_${templateId}`, {
        installedTemplate: templateId,
        templateCategory: template.category,
        projectLanguage: template.language,
        projectFramework: template.framework
      });

      this.recordMetric('success');
      this.recordMetric('installation_time', result.duration);

      const evidence = [
        `Installed template: ${template.name}`,
        `Created ${result.createdFiles.length} files`,
        `Installed ${result.installedDependencies.length} dependencies`,
        `Configured ${result.configuredFiles.length} configuration files`
      ];

      const recommendations = this.generatePostInstallationRecommendations(template, result);

      return {
        success: true,
        message,
        installedTemplate: templateId,
        installedDependencies: result.installedDependencies,
        createdFiles: result.createdFiles,
        evidence,
        recommendations
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Installation failed: ${error.message}`);
    }
  }

  private parseInstallationOptions(args: string[], projectRoot: string): any {
    const options: any = {
      projectRoot,
      projectName: path.basename(projectRoot)
    };

    for (let i = 0; i < args.length; i++) {
      const arg = args[i];
      
      if (arg && arg.startsWith('--name=')) {
        options.projectName = arg.substring('--name='.length);
      } else if (arg && arg.startsWith('--packageManager=')) {
        const manager = arg.substring('--packageManager='.length);
        if (['npm', 'yarn', 'pnpm'].includes(manager)) {
          options.packageManager = manager;
        }
      } else if (arg && arg === '--name' && i + 1 < args.length) {
        options.projectName = args[i + 1];
        i++; // Skip next arg
      } else if (arg && arg === '--packageManager' && i + 1 < args.length) {
        const manager = args[i + 1];
        if (manager && ['npm', 'yarn', 'pnpm'].includes(manager)) {
          options.packageManager = manager;
        }
        i++; // Skip next arg
      }
    }

    return options;
  }

  private generatePostInstallationRecommendations(template: InstallationTemplate, result: InstallationResult): string[] {
    const recommendations: string[] = [];

    // Language-specific recommendations
    if (template.language === 'typescript') {
      recommendations.push('Run type checking with npm run type-check or similar');
    }

    // Framework-specific recommendations  
    if (template.framework === 'react') {
      recommendations.push('Start development server with npm run dev');
      recommendations.push('Consider adding React DevTools browser extension');
    } else if (template.framework === 'express') {
      recommendations.push('Configure environment variables in .env file');
      recommendations.push('Test API endpoints with npm run dev');
    }

    // Category-specific recommendations
    if (template.category === 'web') {
      recommendations.push('Configure linting and formatting tools');
      recommendations.push('Set up pre-commit hooks for code quality');
    } else if (template.category === 'api') {
      recommendations.push('Set up API documentation');
      recommendations.push('Configure logging and monitoring');
    }

    // General recommendations
    if (result.createdFiles.length > 0) {
      recommendations.push('Review and customize generated files as needed');
    }

    if (template.scripts && Object.keys(template.scripts).length > 0) {
      const availableScripts = Object.keys(template.scripts).join(', ');
      recommendations.push(`Available npm scripts: ${availableScripts}`);
    }

    return recommendations.length > 0 ? recommendations : ['Template installation completed successfully'];
  }

  private handleHelp(): InstallerCommandResult {
    const helpMessage = `Installer Command Help

Usage: /ae:installer <action> [options]

Actions:
  • <template-id>        Install a specific template
  • list/templates       List all available templates
  • suggest              Get template suggestions for current project
  • help                 Show this help message

Template Installation:
  /ae:installer typescript-node --name=myproject
  /ae:installer react-vite --packageManager=pnpm
  /ae:installer express-api --name=api-server

Options:
  --name=<name>           Set project name
  --packageManager=<mgr>  Use specific package manager (npm/yarn/pnpm)

Examples:
  /ae:installer list                    # List all templates
  /ae:installer suggest                 # Get recommendations  
  /ae:installer typescript-node         # Install TypeScript Node.js template
  /ae:installer react-vite --name=app   # Install React template with custom name`;

    this.recordMetric('help_requested');
    return {
      success: true,
      message: helpMessage,
      evidence: ['Help information provided'],
      recommendations: ['Use /ae:installer list to see available templates']
    };
  }

  private createErrorResult(message: string): InstallerCommandResult {
    return {
      success: false,
      message,
      evidence: ['Command execution failed'],
      recommendations: ['Use /ae:installer help for usage information']
    };
  }

  // Required abstract method implementations
  protected validateArgs(args: string[]): { isValid: boolean; message?: string } {
    if (args.length === 0) {
      return {
        isValid: false,
        message: 'Please specify an action: template-id, list, suggest, or help'
      };
    }
    return { isValid: true };
  }

  protected async execute(
    args: string[], 
    options: Record<string, any>, 
    context: any
  ): Promise<ExtendedCommandResult> {
    return await this.handler(args, context);
  }

  protected generateValidationClaim(data: any): string {
    if (data.installedTemplate) {
      return `Template "${data.installedTemplate}" was successfully installed`;
    } else if (data.availableTemplates) {
      return `${data.availableTemplates.length} templates are available for installation`;
    }
    return 'Installer operation was completed';
  }

  protected generateSummary(data: any): string {
    if (data.installedTemplate) {
      return `Successfully installed template: ${data.installedTemplate}`;
    } else if (data.availableTemplates) {
      return `Found ${data.availableTemplates.length} available templates`;
    }
    return 'Installer operation completed';
  }
}