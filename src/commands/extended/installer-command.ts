/**
 * Installer Command for ae-framework
 * Provides project template installation and setup functionality
 */

import { BaseExtendedCommand } from './base-command.js';
import type { ExtendedCommandResult, ExtendedCommandConfig } from './base-command.js';
import { INSTALLER_APPROVAL_SCOPE, InstallerManager } from '../../utils/installer-manager.js';
import type {
  InstallationTemplate,
  InstallationResult,
  InstallerApproval,
  PlannedInstallationChange,
} from '../../utils/installer-manager.js';
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
  dryRun?: boolean;
  approvalRequired?: boolean;
  plannedChanges?: PlannedInstallationChange[];
}

export class InstallerCommand extends BaseExtendedCommand {
  public override readonly name = '/ae:installer';
  public override readonly description = 'Install project templates and manage dependencies';
  public override readonly category = 'utility' as const;
  public override readonly usage = '/ae:installer <template-id> | list | suggest | templates';
  public override readonly aliases = ['/installer', '/install', '/a:installer'];

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

  override async handler(args: string[], context: any): Promise<InstallerCommandResult> {
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
          return await this.handleInstallTemplate(
            action,
            args.slice(1),
            installerManager,
            contextManager,
            tokenOptimizer,
            projectRoot,
            context
          );
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

      message += 'Usage: /ae:installer <template-id> to preview a template installation\n';
      message += `Use /ae:installer <template-id> --apply only with ${INSTALLER_APPROVAL_SCOPE} approval\n`;
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
        
        message += `Use /ae:installer <template-id> to preview any of these templates`;
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
    projectRoot: string,
    commandContext: any
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
      const installationContext = this.parseInstallationOptions(additionalArgs, projectRoot, commandContext);

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

        if (result.approvalRequired) {
          return {
            success: false,
            message: errorMessage,
            approvalRequired: true,
            plannedChanges: result.plannedChanges ?? [],
            evidence: [
              'Installer apply was rejected before dependency installation or project writes',
              `Required approval scope: ${INSTALLER_APPROVAL_SCOPE}`,
            ],
            recommendations: [
              `Rerun with --apply only after trusted-operator approval scope "${INSTALLER_APPROVAL_SCOPE}" is present`,
            ],
          };
        }

        return this.createErrorResult(errorMessage);
      }

      if (result.dryRun === true) {
        this.recordMetric('preview');
        let message = `Previewed '${template.name}' template installation (dry run).\n`;
        message += 'No dependencies were installed and no project files were changed.\n\n';

        if (result.plannedChanges && result.plannedChanges.length > 0) {
          message += 'Planned changes:\n';
          result.plannedChanges.forEach(change => {
            const commandPreview = change.command
              ? ` [${[change.command, ...(change.args ?? [])].join(' ')}]`
              : '';
            message += `  • ${change.action}: ${change.target}${commandPreview}\n`;
          });
          message += '\n';
        }

        message += `To apply these changes, rerun with --apply from a context that carries `;
        message += `approval.scope="${INSTALLER_APPROVAL_SCOPE}" and approval.approved=true.`;

        return {
          success: true,
          message,
          dryRun: true,
          plannedChanges: result.plannedChanges ?? [],
          evidence: [
            `Previewed template: ${template.name}`,
            `Planned ${result.plannedChanges?.length ?? 0} installer changes`,
            'No installer writes or package-manager commands were executed'
          ],
          recommendations: [
            `Obtain trusted-operator approval with scope "${INSTALLER_APPROVAL_SCOPE}" before using --apply`
          ]
        };
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
        dryRun: false,
        plannedChanges: result.plannedChanges ?? [],
        evidence,
        recommendations
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Installation failed: ${error.message}`);
    }
  }

  private parseInstallationOptions(args: string[], projectRoot: string, commandContext: any): any {
    const options: any = {
      projectRoot,
      projectName: path.basename(projectRoot),
      dryRun: true
    };

    const approval = this.extractInstallerApproval(commandContext);
    if (approval) {
      options.approval = approval;
    }

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
      } else if (arg === '--apply') {
        options.dryRun = false;
      } else if (arg === '--dry-run' || arg === '--preview') {
        options.dryRun = true;
      } else if (arg === '--allow-lifecycle-scripts') {
        options.allowLifecycleScripts = true;
      }
    }

    return options;
  }

  private extractInstallerApproval(commandContext: any): InstallerApproval | undefined {
    const approval = commandContext?.approval;
    if (approval?.approved === true && approval?.scope === INSTALLER_APPROVAL_SCOPE) {
      return {
        approved: true,
        scope: INSTALLER_APPROVAL_SCOPE,
        ...(typeof approval.approvedBy === 'string' ? { approvedBy: approval.approvedBy } : {}),
        ...(typeof approval.reason === 'string' ? { reason: approval.reason } : {}),
      };
    }
    return undefined;
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
  /ae:installer typescript-node --name=myproject          # Preview only
  /ae:installer react-vite --packageManager=pnpm          # Preview only
  /ae:installer express-api --name=api-server --apply     # Requires trusted approval

Options:
  --name=<name>           Set project name
  --packageManager=<mgr>  Use specific package manager (npm/yarn/pnpm)
  --dry-run/--preview     Preview planned changes without writes or dependency installs (default)
  --apply                 Apply planned changes only when context.approval.scope="${INSTALLER_APPROVAL_SCOPE}"
  --allow-lifecycle-scripts Allow dependency lifecycle scripts during approved package installs

Examples:
  /ae:installer list                    # List all templates
  /ae:installer suggest                 # Get recommendations  
  /ae:installer typescript-node         # Preview TypeScript Node.js template
  /ae:installer react-vite --name=app   # Preview React template with custom name`;

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
  protected override validateArgs(args: string[]): { isValid: boolean; message?: string } {
    if (args.length === 0) {
      return {
        isValid: false,
        message: 'Please specify an action: template-id, list, suggest, or help'
      };
    }
    return { isValid: true };
  }

  protected override async execute(
    args: string[], 
    options: Record<string, any>, 
    context: any
  ): Promise<ExtendedCommandResult> {
    return await this.handler(args, context);
  }

  protected override generateValidationClaim(data: any): string {
    if (data.dryRun) {
      return `Template "${data.installedTemplate ?? 'installer'}" installation was previewed without local changes`;
    }
    if (data.installedTemplate) {
      return `Template "${data.installedTemplate}" was successfully installed`;
    } else if (data.availableTemplates) {
      return `${data.availableTemplates.length} templates are available for installation`;
    }
    return 'Installer operation was completed';
  }

  protected override generateSummary(data: any): string {
    if (data.dryRun) {
      return 'Installer dry-run preview completed without applying changes';
    }
    if (data.installedTemplate) {
      return `Successfully installed template: ${data.installedTemplate}`;
    } else if (data.availableTemplates) {
      return `Found ${data.availableTemplates.length} available templates`;
    }
    return 'Installer operation completed';
  }
}
