/**
 * Setup CLI commands for the AE-Framework
 * Wraps InstallerManager templates for initial project setup.
 */

import { Command } from 'commander';
import chalk from 'chalk';
import path from 'node:path';
import { InstallerManager } from '../utils/installer-manager.js';
import { safeExit } from '../utils/safe-exit.js';

type PackageManager = 'npm' | 'yarn' | 'pnpm';

type SetupOptions = {
  root?: string;
  name?: string;
  packageManager?: string;
};

const PACKAGE_MANAGERS = new Set<PackageManager>(['npm', 'yarn', 'pnpm']);

const normalizePackageManager = (value?: string): PackageManager | undefined => {
  if (!value) return undefined;
  const normalized = value.trim().toLowerCase() as PackageManager;
  return PACKAGE_MANAGERS.has(normalized) ? normalized : undefined;
};

const resolveRoot = (root?: string): string => path.resolve(root || process.cwd());

const renderTemplateList = (manager: InstallerManager): void => {
  const templates = manager.getAvailableTemplates();
  if (templates.length === 0) {
    console.log(chalk.yellow('No templates available.'));
    return;
  }

  console.log(chalk.cyan('Available Templates:'));
  const categories = [...new Set(templates.map(template => template.category))];

  for (const category of categories) {
    console.log(`\n${category.toUpperCase()}:`);
    const categoryTemplates = templates.filter(template => template.category === category);
    for (const template of categoryTemplates) {
      const framework = template.framework ? `, Framework: ${template.framework}` : '';
      console.log(`  • ${template.id} - ${template.name}`);
      console.log(`    ${template.description}`);
      console.log(`    Language: ${template.language}${framework}`);
    }
  }

  console.log('\nUsage: ae setup <template-id> to install a template');
  console.log('Use ae setup suggest for project-specific recommendations');
};

const renderSuggestionList = async (manager: InstallerManager): Promise<void> => {
  const { suggestions, reasoning } = await manager.suggestTemplates();
  if (suggestions.length === 0) {
    console.log(chalk.yellow('No specific suggestions for this project.'));
    console.log('Use ae setup list to see all available templates');
    return;
  }

  console.log(chalk.cyan('Template Suggestions:'));
  suggestions.forEach((templateId, index) => {
    const reason = reasoning[index] ?? 'No reasoning available';
    console.log(`\n${index + 1}. ${templateId}`);
    console.log(`   Reason: ${reason}`);
  });

  console.log('\nUse ae setup <template-id> to install any of these templates');
};

const renderInstallResult = (templateId: string, result: Awaited<ReturnType<InstallerManager['installTemplate']>>): void => {
  if (!result.success) {
    console.error(chalk.red(`❌ Failed to install template '${templateId}': ${result.message}`));
    if (result.errors.length > 0) {
      console.error('\nErrors:');
      result.errors.forEach(error => console.error(`  • ${error}`));
    }
    if (result.warnings.length > 0) {
      console.warn('\nWarnings:');
      result.warnings.forEach(warning => console.warn(`  • ${warning}`));
    }
    safeExit(1);
    return;
  }

  console.log(chalk.green(`✅ Template '${templateId}' installed successfully.`));
  if (result.installedDependencies.length > 0) {
    console.log('\nInstalled dependencies:');
    result.installedDependencies.forEach(dep => console.log(`  • ${dep}`));
  }
  if (result.createdFiles.length > 0) {
    console.log('\nCreated files:');
    result.createdFiles.forEach(file => console.log(`  • ${file}`));
  }
  if (result.configuredFiles.length > 0) {
    console.log('\nConfigured files:');
    result.configuredFiles.forEach(file => console.log(`  • ${file}`));
  }
  if (result.executedSteps.length > 0) {
    console.log('\nExecuted steps:');
    result.executedSteps.forEach(step => console.log(`  • ${step}`));
  }
  if (result.warnings.length > 0) {
    console.warn('\nWarnings:');
    result.warnings.forEach(warning => console.warn(`  • ${warning}`));
  }

  console.log(`\nCompleted in ${result.duration}ms`);
};

export function createSetupCommand(): Command {
  const setup = new Command('setup');
  setup
    .description('Install project templates and guide initial setup')
    .option('--root <path>', 'Project root (default: cwd)', process.cwd());

  setup
    .command('list')
    .description('List available templates')
    .option('--root <path>', 'Project root (default: cwd)')
    .action((options: { root?: string }) => {
      const root = resolveRoot(options.root ?? setup.opts()['root']);
      const manager = new InstallerManager(root);
      renderTemplateList(manager);
    });

  setup
    .command('suggest')
    .description('Suggest templates based on current project')
    .option('--root <path>', 'Project root (default: cwd)')
    .action(async (options: { root?: string }) => {
      const root = resolveRoot(options.root ?? setup.opts()['root']);
      const manager = new InstallerManager(root);
      try {
        await renderSuggestionList(manager);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Failed to suggest templates: ${String(error)}`));
        safeExit(1);
      }
    });

  setup
    .argument('[templateId]', 'Template ID to install')
    .option('--name <projectName>', 'Override project name')
    .option('--package-manager <npm|yarn|pnpm>', 'Override package manager')
    .action(async (templateId: string | undefined, options: SetupOptions) => {
      if (!templateId) {
        setup.outputHelp();
        return;
      }

      const root = resolveRoot(setup.opts()['root']);
      const manager = new InstallerManager(root);
      if (!manager.getTemplate(templateId)) {
        console.error(chalk.red(`❌ Template not found: ${templateId}`));
        console.log('Use ae setup list to see available templates.');
        safeExit(2);
        return;
      }

      const packageManager = normalizePackageManager(options.packageManager);
      if (options.packageManager && !packageManager) {
        console.error(chalk.red(`❌ Invalid package manager: ${options.packageManager}`));
        console.log('Allowed values: npm, yarn, pnpm');
        safeExit(2);
        return;
      }

      const installContext: { projectName?: string; packageManager?: PackageManager } = {};
      if (options.name) {
        installContext.projectName = options.name;
      }
      if (packageManager) {
        installContext.packageManager = packageManager;
      }

      try {
        const result = await manager.installTemplate(templateId, installContext);
        renderInstallResult(templateId, result);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Setup failed: ${String(error)}`));
        safeExit(1);
      }
    });

  return setup;
}
