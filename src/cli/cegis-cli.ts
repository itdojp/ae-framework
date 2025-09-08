/**
 * CEGIS CLI Interface
 * Phase 2.1: Command-line interface for automatic code fixing
 */

import { Command } from 'commander';
import chalk from 'chalk';
import { readFileSync, writeFileSync, existsSync } from 'fs';
import type { join } from 'path';
import { AutoFixEngine } from '../cegis/auto-fix-engine.js';
import type { FailureCategory } from '../cegis/types.js';
import { FailureArtifactFactory } from '../cegis/failure-artifact-factory.js';
import { FailureArtifact, AutoFixOptions } from '../cegis/types.js';
import { toMessage } from '../utils/error-utils.js';

export class CEGISCli {
  private engine: AutoFixEngine;

  constructor() {
    this.engine = new AutoFixEngine();
  }

  /**
   * Create and configure the CLI command
   */
  createCommand(): Command {
    const command = new Command('fix')
      .description('CEGIS-based automated code fixing')
      .version('1.0.0');

    // Main fix command
    command
      .command('apply')
      .description('Apply automated fixes to failure artifacts')
      .option('-i, --input <file>', 'Input failure artifacts JSON file')
      .option('-o, --output <dir>', 'Output directory for fixed files', './cegis-output')
      .option('--dry-run', 'Show proposed fixes without applying them')
      .option('--confidence <threshold>', 'Minimum confidence threshold (0.0-1.0)', '0.7')
      .option('--max-risk <level>', 'Maximum risk level (1-5)', '3')
      .option('--max-fixes <count>', 'Maximum number of fixes to apply', '10')
      .option('--no-backup', 'Skip creating backup files')
      .option('--no-report', 'Skip generating fix report')
      .action(async (options) => {
        await this.handleApplyCommand(options);
      });

    // Analyze command
    command
      .command('analyze')
      .description('Analyze failure patterns without applying fixes')
      .option('-i, --input <file>', 'Input failure artifacts JSON file')
      .option('-v, --verbose', 'Verbose analysis output')
      .option('--output-format <format>', 'Output format (json, markdown)', 'markdown')
      .action(async (options) => {
        await this.handleAnalyzeCommand(options);
      });

    // Create artifacts command
    command
      .command('create-artifact')
      .description('Create failure artifact from error information')
      .option('--type <type>', 'Failure type (error, test, type, contract, build, lint)', 'error')
      .option('--message <message>', 'Error message', '')
      .option('--file <file>', 'Source file path')
      .option('--line <line>', 'Line number', '1')
      .option('--column <column>', 'Column number', '1')
      .option('--output <file>', 'Output file for artifact', 'failure-artifact.json')
      .action(async (options) => {
        await this.handleCreateArtifactCommand(options);
      });

    // Status command
    command
      .command('status')
      .description('Show CEGIS system status and configuration')
      .action(async () => {
        await this.handleStatusCommand();
      });

    // Strategies command
    command
      .command('strategies')
      .description('List available fix strategies')
      .option('--category <category>', 'Filter by failure category')
      .action(async (options) => {
        await this.handleStrategiesCommand(options);
      });

    return command;
  }

  /**
   * Handle the apply command
   */
  private async handleApplyCommand(options: any): Promise<void> {
    try {
      console.log('🔧 Starting CEGIS auto-fix process...');

      // Load failure artifacts
      const failures = await this.loadFailures(options.input);
      if (failures.length === 0) {
        console.log('ℹ️  No failure artifacts found.');
        return;
      }

      console.log(`📋 Loaded ${failures.length} failure artifacts`);

      // Configure auto-fix options
      const autoFixOptions: AutoFixOptions = {
        dryRun: options.dryRun || false,
        confidenceThreshold: parseFloat(options.confidence),
        maxRiskLevel: parseInt(options.maxRisk),
        timeoutMs: 30000
      };

      // Validate options
      const confidenceThreshold = autoFixOptions.confidenceThreshold ?? 0.7;
      const maxRiskLevel = autoFixOptions.maxRiskLevel ?? 3;
      
      if (confidenceThreshold < 0 || confidenceThreshold > 1) {
        console.error(chalk.red('❌ Confidence threshold must be between 0.0 and 1.0'));
        return;
      }

      if (maxRiskLevel < 1 || maxRiskLevel > 5) {
        console.error(chalk.red('❌ Risk level must be between 1 and 5'));
        return;
      }

      // Execute fixes
      const result = await this.engine.executeFixes(failures, autoFixOptions);

      // Display results
      await this.displayResults(result, options);

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Auto-fix failed: ${toMessage(error)}`));
      process.exit(1);
    }
  }

  /**
   * Handle the analyze command
   */
  private async handleAnalyzeCommand(options: any): Promise<void> {
    try {
      console.log('🔍 Analyzing failure patterns...');

      const failures = await this.loadFailures(options.input);
      if (failures.length === 0) {
        console.log('ℹ️  No failure artifacts found.');
        return;
      }

      // Analyze patterns
      const patterns = await this.engine.analyzeFailurePatterns(failures);
      
      console.log(`\n📊 Analysis Results:\n`);
      console.log(`Total Failures: ${failures.length}`);
      console.log(`Patterns Detected: ${patterns.length}\n`);

      if (patterns.length > 0) {
        console.log('🔍 Failure Patterns:');
        for (const pattern of patterns.slice(0, 5)) {
          console.log(`- "${pattern.pattern}" (${pattern.frequency} occurrences, ${(pattern.confidence * 100).toFixed(1)}% confidence)`);
        }
        console.log();
      }

      // Category breakdown
      const categoryGroups = this.groupByCategory(failures);
      console.log('📂 Failure Categories:');
      for (const [category, categoryFailures] of categoryGroups) {
        const percentage = ((categoryFailures.length / failures.length) * 100).toFixed(1);
        console.log(`- ${category}: ${categoryFailures.length} (${percentage}%)`);
      }

      if (options.verbose) {
        console.log('\n📝 Detailed Analysis:');
        for (const failure of failures.slice(0, 3)) {
          console.log(`\n${failure.title}`);
          console.log(`  Category: ${failure.category}`);
          console.log(`  Severity: ${failure.severity}`);
          if (failure.location) {
            console.log(`  Location: ${failure.location.filePath}:${failure.location.startLine}`);
          }
          console.log(`  Actions: ${failure.suggestedActions.length}`);
        }
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Analysis failed: ${toMessage(error)}`));
      process.exit(1);
    }
  }

  /**
   * Handle the create-artifact command
   */
  private async handleCreateArtifactCommand(options: any): Promise<void> {
    try {
      console.log('📝 Creating failure artifact...');

      if (!options.message) {
        console.error(chalk.red('❌ Error message is required'));
        return;
      }

      let artifact: FailureArtifact;

      switch (options.type) {
        case 'error':
          const error = new Error(options.message);
          artifact = FailureArtifactFactory.fromError(
            error,
            options.file ? {
              filePath: options.file,
              startLine: parseInt(options.line),
              endLine: parseInt(options.line),
              startColumn: parseInt(options.column),
              endColumn: parseInt(options.column)
            } : undefined
          );
          break;

        case 'test':
          artifact = FailureArtifactFactory.fromTestFailure(
            'CLI Generated Test Failure',
            'expected',
            'actual',
            options.file ? {
              filePath: options.file,
              startLine: parseInt(options.line),
              endLine: parseInt(options.line)
            } : undefined,
            options.message
          );
          break;

        case 'type':
          artifact = FailureArtifactFactory.fromTypeError(
            options.message,
            options.file || 'unknown.ts',
            parseInt(options.line),
            parseInt(options.column)
          );
          break;

        case 'build':
          artifact = FailureArtifactFactory.fromBuildError(
            options.message,
            'build',
            1,
            options.message
          );
          break;

        default:
          console.error(chalk.red(`❌ Unknown artifact type: ${options.type}`));
          return;
      }

      // Save artifact
      writeFileSync(options.output, JSON.stringify([artifact], null, 2));
      console.log(`✅ Failure artifact created: ${options.output}`);

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to create artifact: ${toMessage(error)}`));
      process.exit(1);
    }
  }

  /**
   * Handle the status command
   */
  private async handleStatusCommand(): Promise<void> {
    console.log('🔧 CEGIS System Status\n');
    console.log(`Version: 1.0.0`);
    console.log(`Engine: AutoFixEngine`);
    
    // Show available strategies
    const allCategories: FailureCategory[] = ['type_error', 'test_failure', 'contract_violation', 'lint_error', 'build_error'];
    console.log('\n📋 Available Strategies:');
    
    for (const category of allCategories) {
      const strategies = this.engine.getStrategies(category as FailureCategory);
      console.log(`- ${category}: ${strategies.length} strategies`);
    }

    console.log('\n⚙️  Configuration:');
    console.log('- Confidence Threshold: 0.7 (default)');
    console.log('- Max Risk Level: 3 (default)');
    console.log('- Max Fixes Per Run: 10 (default)');
    console.log('- Backup Files: true (default)');
    console.log('- Generate Reports: true (default)');
  }

  /**
   * Handle the strategies command
   */
  private async handleStrategiesCommand(options: any): Promise<void> {
    console.log('🛠️  Available Fix Strategies\n');

    const allCategories: FailureCategory[] = ['type_error', 'test_failure', 'contract_violation', 'lint_error', 'build_error'];
    const categoriesToShow: FailureCategory[] = options.category && allCategories.includes(options.category as FailureCategory)
      ? [options.category as FailureCategory]
      : allCategories;

    for (const category of categoriesToShow) {
      const strategies = this.engine.getStrategies(category);
      
      if (strategies.length === 0) {
        console.log(`${category}: No strategies available`);
        continue;
      }

      console.log(`\n📂 ${category.toUpperCase()}:`);
      for (const strategy of strategies) {
        console.log(`- ${strategy.name}`);
        console.log(`  Confidence: ${(strategy.confidence * 100).toFixed(1)}%`);
        console.log(`  Risk Level: ${strategy.riskLevel}/5`);
        console.log(`  Description: ${strategy.description}`);
      }
    }
  }

  /**
   * Load failure artifacts from file
   */
  private async loadFailures(inputFile?: string): Promise<FailureArtifact[]> {
    if (!inputFile) {
      console.log('ℹ️  No input file specified. Use --input to specify failure artifacts.');
      return [];
    }

    if (!existsSync(inputFile)) {
      throw new Error(`Input file not found: ${inputFile}`);
    }

    try {
      const content = readFileSync(inputFile, 'utf-8');
      const data = JSON.parse(content);
      
      // Handle both single artifact and array
      const artifacts = Array.isArray(data) ? data : [data];
      
      // Validate artifacts
      return artifacts.map(artifact => {
        try {
          return FailureArtifactFactory.validate(artifact);
        } catch (error: unknown) {
          console.warn(`⚠️  Invalid artifact skipped: ${toMessage(error)}`);
          return null;
        }
      }).filter(Boolean) as FailureArtifact[];
      
    } catch (error: unknown) {
      throw new Error(`Failed to parse input file: ${toMessage(error)}`);
    }
  }

  /**
   * Display fix results
   */
  private async displayResults(result: any, options: any): Promise<void> {
    console.log('\n📊 Fix Results:\n');
    
    if (options.dryRun) {
      console.log('🔍 DRY RUN - No changes were applied\n');
    }
    
    console.log(`✅ Success: ${result.summary.success ? 'Yes' : 'No'}`);
    console.log(`📋 Total Failures: ${result.summary.totalFailures}`);
    console.log(`🔧 Fixes Applied: ${result.summary.fixesApplied}`);
    console.log(`⏭️  Fixes Skipped: ${result.summary.fixesSkipped}`);
    console.log(`📁 Files Modified: ${result.summary.filesModified}`);

    if (result.summary.errors.length > 0) {
      console.log('\n❌ Errors:');
      for (const error of result.summary.errors) {
        console.log(`- ${error}`);
      }
    }

    if (result.summary.warnings.length > 0) {
      console.log('\n⚠️  Warnings:');
      for (const warning of result.summary.warnings) {
        console.log(`- ${warning}`);
      }
    }

    if (result.recommendations.length > 0) {
      console.log('\n💡 Recommendations:');
      for (const rec of result.recommendations) {
        console.log(`- ${rec}`);
      }
    }

    if (result.reportPath) {
      console.log(`\n📄 Full report: ${result.reportPath}`);
    }
  }

  /**
   * Group failures by category
   */
  private groupByCategory(failures: FailureArtifact[]): Map<string, FailureArtifact[]> {
    const groups = new Map<string, FailureArtifact[]>();
    
    for (const failure of failures) {
      const category = failure.category;
      if (!groups.has(category)) {
        groups.set(category, []);
      }
      groups.get(category)!.push(failure);
    }
    
    return groups;
  }
}

/**
 * Execute the CEGIS CLI
 */
export async function executeCEGISCli(args: string[]): Promise<void> {
  const cli = new CEGISCli();
  const command = cli.createCommand();
  
  try {
    await command.parseAsync(args);
  } catch (error: unknown) {
    console.error(chalk.red(`❌ CLI execution failed: ${toMessage(error)}`));
    process.exit(1);
  }
}
