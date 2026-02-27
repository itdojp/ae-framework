/**
 * CEGIS CLI Interface
 * Phase 2.1: Command-line interface for automatic code fixing
 */

import { Command } from 'commander';
import chalk from 'chalk';
import { readFileSync, writeFileSync, existsSync, mkdirSync } from 'fs';
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { v4 as uuidv4 } from 'uuid';
import { AutoFixEngine } from '../cegis/auto-fix-engine.js';
import type { FailureCategory } from '../cegis/types.js';
import { FailureArtifactFactory } from '../cegis/failure-artifact-factory.js';
import type { FailureArtifact, AutoFixOptions } from '../cegis/types.js';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import { loadConfig } from '../core/config.js';

interface ConformanceViolationInput {
  ruleId?: string;
  ruleName?: string;
  category?: string;
  severity?: string;
  message?: string;
  actualValue?: unknown;
  expectedValue?: unknown;
  context?: {
    timestamp?: string;
    executionId?: string;
    environment?: string;
    functionName?: string;
    modulePath?: string;
    line?: number;
    column?: number;
    traceId?: string;
    metadata?: Record<string, unknown>;
  };
  stackTrace?: string;
  evidence?: {
    inputData?: unknown;
    outputData?: unknown;
    stateSnapshot?: Record<string, unknown>;
    metrics?: Record<string, number>;
    logs?: string[];
    traces?: unknown[];
  };
  remediation?: {
    suggested?: string[];
    automatic?: boolean;
    priority?: 'low' | 'medium' | 'high' | 'critical';
  };
}

interface ConformanceVerifyResultInput {
  violations?: ConformanceViolationInput[];
  metadata?: {
    environment?: string;
    timestamp?: string;
    executionId?: string;
    version?: string;
  };
}

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
      .option('--apply', 'Apply fixes even when mode=copilot')
      .option('--confidence <threshold>', 'Minimum confidence threshold (0.0-1.0)', '0.7')
      .option('--max-risk <level>', 'Maximum risk level (1-5)', '3')
      .option('--max-fixes <count>', 'Maximum number of fixes to apply', '10')
      .option('--no-backup', 'Skip creating backup files')
      .option('--no-report', 'Skip generating fix report')
      .option('--verify', 'Run verify profile after apply')
      .option('--verify-profile <name>', 'Verify profile to run', 'lite')
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

    // Convert conformance result command
    command
      .command('from-conformance')
      .description('Convert conformance verify result JSON into failure artifacts for ae fix apply')
      .option(
        '-i, --input <file>',
        'Input conformance verify result JSON file',
        path.join('artifacts', 'conformance', 'conformance-results.json')
      )
      .option(
        '-o, --output <file>',
        'Output failure artifacts JSON file',
        path.join('artifacts', 'fix', 'failures.json')
      )
      .action(async (options) => {
        await this.handleFromConformanceCommand(options);
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
      const config = await loadConfig();
      const mode = config.mode ?? 'copilot';
      const enforcedDryRun = mode === 'copilot' && !options.apply;
      const dryRun = Boolean(options.dryRun || enforcedDryRun);
      options.dryRun = dryRun;
      if (enforcedDryRun) {
        console.log('[ae:fix] copilot mode defaults to dry-run. Use --apply to execute fixes.');
      }

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
        dryRun,
        confidenceThreshold: parseFloat(options.confidence),
        maxRiskLevel: parseInt(options.maxRisk, 10),
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

      const shouldVerify = mode === 'delegated' || Boolean(options.verify);
      if (shouldVerify && !dryRun) {
        const profile = options.verifyProfile || 'lite';
        const verifyScript = path.join(process.cwd(), 'scripts', 'verify', 'run.mjs');
        if (!existsSync(verifyScript)) {
          console.error(chalk.red(`❌ verify runner not found: ${verifyScript}`));
          safeExit(1);
          return;
        }

        console.log(chalk.blue(`🔍 Running verify profile: ${profile}`));
        const verifyResult = spawnSync(process.execPath, [verifyScript, '--profile', profile], {
          stdio: 'inherit',
          env: process.env,
        });
        if (verifyResult.error) {
          console.error(chalk.red(`❌ verify failed to start: ${toMessage(verifyResult.error)}`));
          safeExit(1);
          return;
        }
        if (verifyResult.status && verifyResult.status !== 0) {
          safeExit(verifyResult.status);
          return;
        }
      } else if (shouldVerify && dryRun) {
        console.log(chalk.yellow('ℹ️  Dry-run mode: skipping verify run.'));
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Auto-fix failed: ${toMessage(error)}`));
      safeExit(1);
      throw error instanceof Error ? error : new Error(String(error));
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
      safeExit(1);
      throw error instanceof Error ? error : new Error(String(error));
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
      safeExit(1);
      throw error instanceof Error ? error : new Error(String(error));
    }
  }

  /**
   * Handle conversion from conformance verify result to CEGIS failure artifacts
   */
  private async handleFromConformanceCommand(options: any): Promise<void> {
    try {
      console.log('🧪 Converting conformance violations to failure artifacts...');

      if (!options.input || !existsSync(options.input)) {
        throw new Error(`Conformance result file not found: ${options.input}`);
      }

      const content = readFileSync(options.input, 'utf-8');
      const parsed = JSON.parse(content) as ConformanceVerifyResultInput;
      const violations = Array.isArray(parsed.violations) ? parsed.violations : [];

      const failures = violations.map((violation, index) =>
        FailureArtifactFactory.validate(
          this.convertViolationToFailureArtifact(violation, parsed.metadata, index),
        ),
      );

      const outputDir = path.dirname(options.output);
      mkdirSync(outputDir, { recursive: true });
      writeFileSync(options.output, JSON.stringify(failures, null, 2));

      console.log(`📋 Conformance violations: ${violations.length}`);
      console.log(`✅ Generated failure artifacts: ${failures.length}`);
      console.log(`📁 Saved converted artifacts: ${options.output}`);
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to convert conformance result: ${toMessage(error)}`));
      safeExit(1);
      throw error instanceof Error ? error : new Error(String(error));
    }
  }

  private convertViolationToFailureArtifact(
    violation: ConformanceViolationInput,
    resultMetadata: ConformanceVerifyResultInput['metadata'],
    index: number,
  ): FailureArtifact {
    const now = new Date().toISOString();
    const traceId = this.extractTraceId(violation);
    const ruleId = violation.ruleId || `unknown-rule-${index + 1}`;
    const ruleName = violation.ruleName || ruleId;
    const message = violation.message || 'Conformance violation detected';
    const counterexampleKey = `${ruleId}|${traceId || 'no-trace'}|${message}`;
    const location = this.extractLocationFromViolation(violation);
    const violationType = this.inferContractViolationType(violation);
    const contractName = ruleName;
    const actualData = violation.evidence?.inputData ?? violation.evidence?.outputData ?? violation.actualValue;

    const evidenceLogs: string[] = [
      ...(violation.evidence?.logs ?? []),
      `Contract: ${contractName}`,
      `Violation type: ${violationType}`,
    ];
    if (actualData !== undefined) {
      evidenceLogs.push(`Actual data: ${this.safeJsonSerialize(actualData)}`);
    }
    if (violation.evidence?.stateSnapshot !== undefined) {
      evidenceLogs.push(`stateSnapshot=${this.safeSerialize(violation.evidence.stateSnapshot)}`);
    }
    if (violation.evidence?.inputData !== undefined) {
      evidenceLogs.push(`inputData=${this.safeSerialize(violation.evidence.inputData)}`);
    }
    if (violation.evidence?.outputData !== undefined) {
      evidenceLogs.push(`outputData=${this.safeSerialize(violation.evidence.outputData)}`);
    }
    for (const [traceIndex, trace] of (violation.evidence?.traces ?? []).entries()) {
      evidenceLogs.push(`trace[${traceIndex}]=${this.safeSerialize(trace)}`);
    }

    const remediationSuggestions = violation.remediation?.suggested ?? [];
    const suggestedActions = remediationSuggestions.map((suggestion) => ({
      type: 'validation_update' as const,
      description: suggestion,
      confidence: violation.remediation?.automatic ? 0.85 : 0.65,
      riskLevel: this.mapRemediationPriorityToRiskLevel(violation.remediation?.priority),
      estimatedEffort: this.mapRemediationPriorityToEffort(violation.remediation?.priority),
      filePath: violation.context?.modulePath,
      dependencies: [],
      prerequisites: [],
    }));

    return {
      id: uuidv4(),
      title: `Conformance Violation: ${ruleName}`,
      description: message,
      severity: this.mapConformanceSeverityToFailureSeverity(violation.severity),
      category: this.mapConformanceCategoryToFailureCategory(violation.category),
      location,
      context: {
        environment:
          violation.context?.environment || resultMetadata?.environment || process.env['NODE_ENV'] || 'runtime',
        nodeVersion: process.version,
        timestamp: violation.context?.timestamp || resultMetadata?.timestamp || now,
        phase: 'verify',
        command: 'ae conformance verify',
      },
      evidence: {
        stackTrace: violation.stackTrace,
        errorMessage: message,
        errorType: 'ConformanceViolation',
        logs: evidenceLogs,
        metrics: violation.evidence?.metrics ?? {},
        dependencies: [],
        relatedFiles: violation.context?.modulePath ? [violation.context.modulePath] : [],
      },
      suggestedActions,
      relatedArtifacts: [],
      metadata: {
        createdAt: now,
        updatedAt: now,
        version: '1.0.0',
        tags: [
          'conformance',
          `rule:${ruleId}`,
          `category:${violation.category ?? 'unknown'}`,
          `severity:${violation.severity ?? 'unknown'}`,
          traceId ? `trace:${traceId}` : 'trace:none',
        ],
        source: 'conformance_verify',
        environment: {
          contractName,
          violationType,
          expectedSchema: ruleId,
          ruleId,
          ruleName,
          conformanceCategory: violation.category ?? 'unknown',
          conformanceSeverity: violation.severity ?? 'unknown',
          traceId: traceId || '',
          executionId: violation.context?.executionId || resultMetadata?.executionId || '',
          counterexampleKey,
          actualValue: this.safeSerialize(violation.actualValue),
          expectedValue: this.safeSerialize(violation.expectedValue),
        },
      },
    };
  }

  private mapConformanceCategoryToFailureCategory(category?: string): FailureCategory {
    switch (category) {
      case 'security_policy':
        return 'security_violation';
      case 'performance_constraint':
      case 'resource_usage':
        return 'performance_issue';
      case 'integration_requirement':
        return 'dependency_issue';
      default:
        return 'contract_violation';
    }
  }

  private mapConformanceSeverityToFailureSeverity(
    severity?: string,
  ): FailureArtifact['severity'] {
    switch (severity) {
      case 'critical':
        return 'critical';
      case 'major':
        return 'major';
      case 'minor':
        return 'minor';
      case 'warning':
      case 'info':
      default:
        return 'info';
    }
  }

  private mapRemediationPriorityToRiskLevel(priority?: string): number {
    switch (priority) {
      case 'critical':
        return 5;
      case 'high':
        return 4;
      case 'medium':
        return 3;
      case 'low':
      default:
        return 2;
    }
  }

  private mapRemediationPriorityToEffort(
    priority?: string,
  ): 'low' | 'medium' | 'high' {
    switch (priority) {
      case 'critical':
      case 'high':
        return 'high';
      case 'medium':
        return 'medium';
      case 'low':
      default:
        return 'low';
    }
  }

  private inferContractViolationType(violation: ConformanceViolationInput): 'input' | 'output' | 'schema' {
    const metadataType = violation.context?.metadata?.['violationType'];
    if (metadataType === 'input' || metadataType === 'output' || metadataType === 'schema') {
      return metadataType;
    }

    const hasInput = violation.evidence?.inputData !== undefined;
    const hasOutput = violation.evidence?.outputData !== undefined;
    if (hasInput && !hasOutput) {
      return 'input';
    }
    if (!hasInput && hasOutput) {
      return 'output';
    }
    return 'schema';
  }

  private extractLocationFromViolation(
    violation: ConformanceViolationInput,
  ): FailureArtifact['location'] {
    const rawModulePath = violation.context?.modulePath?.trim();
    if (!rawModulePath) {
      return undefined;
    }

    const parsed = rawModulePath.match(/^(.*?):([0-9]+)(?::([0-9]+))?$/);
    const filePath = parsed?.[1] || rawModulePath;
    const explicitLine = parsed?.[2] ? Number.parseInt(parsed[2], 10) : undefined;
    const explicitColumn = parsed?.[3] ? Number.parseInt(parsed[3], 10) : undefined;

    const metadata = violation.context?.metadata;
    const metadataLine = this.toPositiveInt(metadata?.['line']);
    const metadataColumn = this.toPositiveInt(metadata?.['column']);
    const contextLine = this.toPositiveInt(violation.context?.line);
    const contextColumn = this.toPositiveInt(violation.context?.column);

    const startLine = explicitLine || contextLine || metadataLine || 1;
    const startColumn = explicitColumn || contextColumn || metadataColumn;

    return {
      filePath,
      startLine,
      endLine: startLine,
      ...(startColumn ? { startColumn, endColumn: startColumn } : {}),
    };
  }

  private toPositiveInt(value: unknown): number | undefined {
    if (typeof value === 'number' && Number.isInteger(value) && value > 0) {
      return value;
    }
    if (typeof value === 'string' && value.trim().length > 0) {
      const parsed = Number.parseInt(value, 10);
      if (Number.isInteger(parsed) && parsed > 0) {
        return parsed;
      }
    }
    return undefined;
  }

  private extractTraceId(violation: ConformanceViolationInput): string | undefined {
    const traceIdFromContext = violation.context?.traceId;
    if (typeof traceIdFromContext === 'string' && traceIdFromContext.trim().length > 0) {
      return traceIdFromContext.trim();
    }

    const metadata = violation.context?.metadata;
    if (!metadata || typeof metadata !== 'object') {
      return undefined;
    }

    const candidate = metadata['traceId'];
    if (typeof candidate === 'string' && candidate.trim().length > 0) {
      return candidate.trim();
    }

    return undefined;
  }

  private safeSerialize(value: unknown): string {
    if (typeof value === 'string') {
      return value;
    }
    if (typeof value === 'number' || typeof value === 'boolean' || value === null) {
      return String(value);
    }
    if (value === undefined) {
      return '';
    }
    try {
      return JSON.stringify(value);
    } catch {
      return '[unserializable]';
    }
  }

  private safeJsonSerialize(value: unknown): string {
    try {
      return JSON.stringify(value);
    } catch {
      return 'null';
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
    if (options.category && !allCategories.includes(options.category as FailureCategory)) {
      console.log(`${options.category}: No strategies available`);
      return;
    }
    const categoriesToShow: FailureCategory[] = options.category
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
          console.log(`⚠️  Invalid artifact skipped: ${toMessage(error)}`);
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
    safeExit(1);
  }
}
