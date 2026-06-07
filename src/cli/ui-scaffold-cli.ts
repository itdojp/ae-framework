#!/usr/bin/env node

import { Command } from 'commander';
import * as fs from 'fs';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import { UIScaffoldGenerator } from '../generators/ui-scaffold-generator.js';
import { assertWithinWorkspace, resolveWorkspacePath, resolveWorkspaceRoot } from '../utils/workspace-path-policy.js';
import {
  DEFAULT_HIGH_IMPACT_APPROVAL_SCOPES,
  evaluateHighImpactActionPolicy,
  formatHighImpactDecisionMessage,
} from '../utils/high-impact-action-policy.js';

const program = new Command();
const UI_SCAFFOLD_MATERIALIZE_APPROVAL_SCOPE = DEFAULT_HIGH_IMPACT_APPROVAL_SCOPES['codegen-materialize'];

program
  .name('ae-ui scaffold')
  .description('Generate UI components from Phase State')
  .version('1.0.0');

program
  .command('generate')
  .description('Generate UI components for all entities in phase state')
  .option('-s, --state <path>', 'Path to phase-state.json file', '.ae/phase-state.json')
  .option('-o, --output <path>', 'Output directory for generated files', '.')
  .option('-e, --entity <name>', 'Generate for specific entity only')
  .option('--dry-run', 'Show what would be generated without creating files')
  .option('--apply', `Materialize generated UI files after approval (${UI_SCAFFOLD_MATERIALIZE_APPROVAL_SCOPE})`)
  .option('--approval-scope <scope>', `Trusted UI scaffold materialization approval scope (${UI_SCAFFOLD_MATERIALIZE_APPROVAL_SCOPE})`)
  .option('--overwrite', 'Overwrite existing files')
  .action(async (options) => {
    try {
      console.log(chalk.blue('🎨 ae-ui scaffold - UI Generation Tool'));
      console.log(chalk.gray('─'.repeat(50)));

      const workspaceRoot = resolveWorkspaceRoot({ envVar: 'AE_UI_SCAFFOLD_WORKSPACE_ROOT' });
      const materializationPolicy = evaluateHighImpactActionPolicy({
        actionKind: 'codegen-materialize',
        actionName: 'ae-ui scaffold generate',
        apply: options.apply === true,
        dryRun: options.dryRun === true,
        ...(options.approvalScope !== undefined ? { approvalScope: options.approvalScope } : {}),
        requiredApprovalScope: UI_SCAFFOLD_MATERIALIZE_APPROVAL_SCOPE,
      });
      if (
        materializationPolicy.blocked ||
        materializationPolicy.approvalRequired ||
        (!materializationPolicy.allowed && !materializationPolicy.dryRun)
      ) {
        console.error(chalk.red(`✗ ${formatHighImpactDecisionMessage(materializationPolicy)}`));
        safeExit(1);
        return;
      }
      if (materializationPolicy.dryRun) {
        console.log(chalk.yellow(`⚠️  ${formatHighImpactDecisionMessage(materializationPolicy)}`));
      }

      // Load phase state
      const stateFile = resolveWorkspacePath(options.state, { workspaceRoot, label: 'UI scaffold state file' });
      if (!fs.existsSync(stateFile)) {
        console.error(chalk.red(`✗ Phase state file not found: ${stateFile}`));
        console.log(chalk.yellow('  Run this command from your project root, or specify --state path'));
        safeExit(1);
        return;
      }

      const phaseState = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
      console.log(chalk.green(`✓ Loaded phase state from: ${stateFile}`));

      // Initialize generator
      const generator = new UIScaffoldGenerator(phaseState, {
        outputDir: assertWithinWorkspace(options.output, { workspaceRoot, label: 'UI scaffold output directory' }),
        dryRun: materializationPolicy.dryRun,
        overwrite: options.overwrite,
        targetEntity: options.entity
      });

      // Generate UI components
      const results = await generator.generateAll();

      // Report results
      console.log(chalk.gray('─'.repeat(50)));
      console.log(chalk.blue('📊 Generation Summary:'));
      
      for (const [entityName, result] of Object.entries(results)) {
        console.log(chalk.cyan(`\n${entityName}:`));
        
        if (result.success) {
          result.files.forEach(file => {
            const status = materializationPolicy.dryRun ? '(would create)' : '✓';
            console.log(chalk.green(`  ${status} ${file}`));
          });
        } else {
          console.log(chalk.red(`  ✗ Failed: ${result.error}`));
        }
      }

      const totalFiles = Object.values(results)
        .filter(r => r.success)
        .reduce((sum, r) => sum + r.files.length, 0);

      console.log(chalk.gray('─'.repeat(50)));
      if (materializationPolicy.dryRun) {
        console.log(chalk.yellow(`🔍 Dry run completed. Would generate ${totalFiles} files.`));
        console.log(chalk.gray(`  Rerun with --apply --approval-scope ${UI_SCAFFOLD_MATERIALIZE_APPROVAL_SCOPE} from a trusted workspace/ref to create files.`));
      } else {
        console.log(chalk.green(`🎉 Successfully generated ${totalFiles} files!`));
        console.log(chalk.gray('  Run npm run lint to ensure code quality.'));
      }

    } catch (error: unknown) {
      console.error(chalk.red('✗ Generation failed:'), toMessage(error));
      if (error instanceof Error && error.stack) {
        console.error(chalk.gray(error.stack));
      }
      safeExit(1);
    }
  });

program
  .command('list')
  .description('List entities available for UI generation')
  .option('-s, --state <path>', 'Path to phase-state.json file', '.ae/phase-state.json')
  .action(async (options) => {
    try {
      const workspaceRoot = resolveWorkspaceRoot({ envVar: 'AE_UI_SCAFFOLD_WORKSPACE_ROOT' });
      const stateFile = resolveWorkspacePath(options.state, { workspaceRoot, label: 'UI scaffold state file' });
      if (!fs.existsSync(stateFile)) {
        console.error(chalk.red(`✗ Phase state file not found: ${stateFile}`));
        safeExit(1);
        return;
      }

      const phaseState = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
      const entities = Object.keys(phaseState.entities || {});

      console.log(chalk.blue('📋 Available Entities:'));
      console.log(chalk.gray('─'.repeat(30)));
      
      if (entities.length === 0) {
        console.log(chalk.yellow('  No entities found in phase state'));
      } else {
        entities.forEach(entity => {
          const entityData = phaseState.entities[entity];
          console.log(chalk.cyan(`  ${entity}`));
          console.log(chalk.gray(`    ${entityData.description || 'No description'}`));
          console.log(chalk.gray(`    Attributes: ${Object.keys(entityData.attributes || {}).length}`));
        });
      }

    } catch (error: unknown) {
      console.error(chalk.red('✗ Failed to list entities:'), toMessage(error));
      safeExit(1);
    }
  });

program
  .command('validate')
  .description('Validate phase state for UI generation')
  .option('-s, --state <path>', 'Path to phase-state.json file', '.ae/phase-state.json')
  .action(async (options) => {
    try {
      const workspaceRoot = resolveWorkspaceRoot({ envVar: 'AE_UI_SCAFFOLD_WORKSPACE_ROOT' });
      const stateFile = resolveWorkspacePath(options.state, { workspaceRoot, label: 'UI scaffold state file' });
      if (!fs.existsSync(stateFile)) {
        console.error(chalk.red(`✗ Phase state file not found: ${stateFile}`));
        safeExit(1);
        return;
      }

      const phaseState = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
      const generator = new UIScaffoldGenerator(phaseState, { outputDir: './temp', dryRun: true });
      
      console.log(chalk.blue('🔍 Validating Phase State...'));
      console.log(chalk.gray('─'.repeat(40)));

      const validation = generator.validatePhaseState();
      
      if (validation.valid) {
        console.log(chalk.green('✓ Phase state is valid for UI generation'));
        console.log(chalk.gray(`  Found ${validation.entityCount} entities`));
        console.log(chalk.gray(`  UI preferences: ${validation.uiFramework}`));
      } else {
        console.log(chalk.red('✗ Phase state validation failed:'));
        validation.errors.forEach(error => {
          console.log(chalk.red(`  • ${error}`));
        });
        process.exit(1);
      }

    } catch (error: unknown) {
      console.error(chalk.red('✗ Validation failed:'), toMessage(error));
      safeExit(1);
    }
  });

// Handle unknown commands
program.on('command:*', () => {
  console.error(chalk.red('✗ Unknown command. Available commands:'));
  console.log(chalk.gray('  generate  - Generate UI components'));
  console.log(chalk.gray('  list      - List available entities'));
  console.log(chalk.gray('  validate  - Validate phase state'));
  safeExit(1);
});

// Show help if no command provided
if (process.argv.length <= 2) {
  program.help();
}

program.parse();
