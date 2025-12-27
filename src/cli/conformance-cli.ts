/**
 * Conformance CLI Interface
 * Phase 2.2: Command-line interface for runtime conformance verification
 */

import { Command } from 'commander';
import { readFileSync, writeFileSync, existsSync, mkdirSync, statSync } from 'fs';
import { ConformanceVerificationEngine } from '../conformance/verification-engine.js';
import path from 'node:path';
import { randomBytes, randomUUID } from 'node:crypto';
import { createEncryptedChatDefaultRules } from '../conformance/default-rules.js';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import { glob } from 'glob';
import type { 
  ConformanceRule, 
  ConformanceConfig, 
  RuntimeContext,
  ConformanceRuleCategory,
} from '../conformance/types.js';
import type { 
  ViolationSeverity, 
  ConformanceVerificationResult,
  VerificationStatus,
  ViolationDetails
} from '../conformance/types.js';

const REPORT_SCHEMA_VERSION = '1.0.0';
const DEFAULT_REPORT_DIR = 'reports/conformance';
const DEFAULT_REPORT_JSON = path.join(DEFAULT_REPORT_DIR, 'conformance-summary.json');
const DEFAULT_REPORT_MARKDOWN = path.join(DEFAULT_REPORT_DIR, 'conformance-summary.md');
const VIOLATION_SEVERITIES = ['critical', 'major', 'minor', 'info', 'warning'] as ViolationSeverity[];
const CONFORMANCE_CATEGORIES = [
  'data_validation',
  'api_contract',
  'business_logic',
  'security_policy',
  'performance_constraint',
  'resource_usage',
  'state_invariant',
  'behavioral_constraint',
  'integration_requirement',
  'compliance_rule'
] as ConformanceRuleCategory[];

type ConformanceReportStatus = 'success' | 'failure' | 'skipped';

interface AggregatedRunInput {
  file: string;
  absolutePath: string;
  result: ConformanceVerificationResult;
  timestamp: string;
}

interface ConformanceReportSummary {
  schemaVersion: string;
  generatedAt: string;
  status: ConformanceReportStatus;
  runsAnalyzed: number;
  statusBreakdown: Record<VerificationStatus, number>;
  totals: {
    rulesExecuted: number;
    rulesPassed: number;
    rulesFailed: number;
    rulesErrored: number;
    rulesSkipped: number;
    totalViolations: number;
    uniqueRules: number;
    uniqueViolationRules: number;
  };
  severityTotals: Record<ViolationSeverity, number>;
  categoryTotals: Record<ConformanceRuleCategory, number>;
  severityTrends: Array<{
    severity: ViolationSeverity;
    current: number;
    previous: number;
    trend: 'increasing' | 'decreasing' | 'stable';
  }>;
  topViolations: Array<{
    ruleId: string;
    ruleName: string;
    count: number;
    lastObserved: string | null;
  }>;
  latestRun?: {
    file: string;
    timestamp: string;
    status: VerificationStatus;
    environment: string;
    version: string;
    rulesExecuted: number;
    rulesFailed: number;
    totalViolations: number;
  };
  inputs: Array<{
    file: string;
    timestamp: string;
    status: VerificationStatus;
    environment: string;
    version: string;
    totalViolations: number;
  }>;
  notes?: string;
}

export class ConformanceCli {
  private engine: ConformanceVerificationEngine;
  private config: ConformanceConfig;

  constructor() {
    this.config = this.loadDefaultConfig();
    this.engine = new ConformanceVerificationEngine(this.config);
  }

  /**
   * Create and configure the CLI command
   */
  createCommand(): Command {
    const command = new Command('conformance')
      .description('Runtime conformance verification system')
      .version('2.2.0');

    // Verify command - main verification function
    command
      .command('verify')
      .description('Verify data against conformance rules')
      .option('-i, --input <file>', 'Input data JSON file')
      .option('-r, --rules <file>', 'Rules configuration file')
      .option('-o, --output <file>', 'Output results file', 'conformance-results.json')
      .option('--rule-ids <ids>', 'Specific rule IDs to execute (comma-separated)')
      .option('--skip-categories <categories>', 'Categories to skip (comma-separated)')
      .option('--context-file <file>', 'Runtime context JSON file')
      .option('--format <format>', 'Output format (json, markdown)', 'json')
      .option('--verbose', 'Verbose output')
      .action(async (options) => {
        await this.handleVerifyCommand(options);
      });

    // Rules management
    command
      .command('rules')
      .description('Manage conformance rules')
      .option('-l, --list', 'List all rules')
      .option('-c, --category <category>', 'Filter by category')
      .option('-a, --add <file>', 'Add rules from JSON file')
      .option('-r, --remove <id>', 'Remove rule by ID')
      .option('--export <file>', 'Export rules to file')
      .option('--import <file>', 'Import rules from file')
      .action(async (options) => {
        await this.handleRulesCommand(options);
      });

    // Config management
    command
      .command('config')
      .description('Manage engine configuration')
      .option('-s, --show', 'Show current configuration')
      .option('-u, --update <file>', 'Update configuration from JSON file')
      .option('--set <key=value>', 'Set configuration value')
      .option('--export <file>', 'Export configuration to file')
      .option('--reset', 'Reset to default configuration')
      .action(async (options) => {
        await this.handleConfigCommand(options);
      });

    // Metrics and monitoring
    command
      .command('metrics')
      .description('View conformance metrics')
      .option('--reset', 'Reset metrics counters')
      .option('--export <file>', 'Export metrics to file')
      .option('--format <format>', 'Output format (json, table)', 'table')
      .action(async (options) => {
        await this.handleMetricsCommand(options);
      });

    // Status command
    command
      .command('status')
      .description('Show system status')
      .option('--monitors', 'Show monitor information')
      .option('--handlers', 'Show violation handler information')
      .action(async (options) => {
        await this.handleStatusCommand(options);
      });

    // Generate sample data
    command
      .command('sample')
      .description('Generate sample configurations and data')
      .option('--rules <file>', 'Generate sample rules file', 'sample-rules.json')
      .option('--config <file>', 'Generate sample config file', 'sample-config.json')
      .option('--data <file>', 'Generate sample data file', 'sample-data.json')
      .option('--context <file>', 'Generate sample context file', 'sample-context.json')
      .action(async (options) => {
        await this.handleSampleCommand(options);
      });

    command
      .command('report')
      .description('Generate aggregated conformance report')
      .option('-i, --inputs <files...>', 'Conformance result files to include')
      .option('-g, --glob <patterns...>', 'Glob pattern(s) for locating result files')
      .option('-d, --directory <dir>', 'Directory to search for result files', 'hermetic-reports/conformance')
      .option('-p, --pattern <glob>', 'Glob pattern when using --directory', '*.json')
      .option('-f, --format <format>', 'Output format (json, markdown, both)', 'json')
      .option('-o, --output <file>', 'JSON output file path', DEFAULT_REPORT_JSON)
      .option('--markdown-output <file>', 'Markdown output file path', DEFAULT_REPORT_MARKDOWN)
      .option('--no-default-discovery', 'Disable default result discovery locations')
      .action(async (options) => {
        await this.handleReportCommand(options);
      });

    return command;
  }

  /**
   * Handle the verify command
   */
  private async handleVerifyCommand(options: any): Promise<void> {
    try {
      console.log('🔍 Starting conformance verification...');

      // Load input data
      if (!options.input) {
        console.error(chalk.red('❌ Input file is required. Use --input to specify the data file.'));
        return;
      }

      if (!existsSync(options.input)) {
        console.error(chalk.red(`❌ Input file not found: ${options.input}`));
        return;
      }

      const inputData = JSON.parse(readFileSync(options.input, 'utf-8'));
      console.log(`📄 Loaded input data from ${options.input}`);

      // Load runtime context
      let context: RuntimeContext;
      if (options.contextFile && existsSync(options.contextFile)) {
        context = JSON.parse(readFileSync(options.contextFile, 'utf-8'));
        console.log(`📋 Loaded context from ${options.contextFile}`);
      } else {
        context = this.createDefaultContext();
      }

      // Load custom rules if specified
      if (options.rules && existsSync(options.rules)) {
        const rules: ConformanceRule[] = JSON.parse(readFileSync(options.rules, 'utf-8'));
        console.log(`📜 Loading ${rules.length} custom rules...`);
        
        for (const rule of rules) {
          await this.engine.addRule(rule);
        }
      }

      // Parse options
      const verifyOptions = {
        ruleIds: options.ruleIds ? options.ruleIds.split(',').map((s: string) => s.trim()) : undefined,
        skipCategories: options.skipCategories ? 
          options.skipCategories.split(',').map((s: string) => s.trim() as ConformanceRuleCategory) : undefined,
        async: true
      };

      // Start engine and perform verification
      await this.engine.start();
      console.log('🚀 Engine started, running verification...');

      const result = await this.engine.verify(inputData, context, verifyOptions);
      
      // Stop engine
      await this.engine.stop();

      // Display results
      await this.displayVerificationResults(result, options);

      // Save results
      if (options.format === 'json') {
        writeFileSync(options.output, JSON.stringify(result, null, 2));
        console.log(`💾 Results saved to ${options.output}`);
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Verification failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Handle the rules command
   */
  private async handleRulesCommand(options: any): Promise<void> {
    try {
      if (options.list) {
        const rules = this.engine.getRules();
        console.log(`📜 Found ${rules.length} conformance rules:\n`);
        
        const filteredRules = options.category 
          ? rules.filter(r => r.category === options.category)
          : rules;

        for (const rule of filteredRules) {
          console.log(`🔸 ${rule.name} (${rule.id})`);
          console.log(`   Category: ${rule.category}`);
          console.log(`   Severity: ${rule.severity}`);
          console.log(`   Enabled: ${rule.enabled ? '✅' : '❌'}`);
          console.log(`   Description: ${rule.description}`);
          console.log('');
        }
      }

      if (options.add && existsSync(options.add)) {
        const newRules: ConformanceRule[] = JSON.parse(readFileSync(options.add, 'utf-8'));
        console.log(`➕ Adding ${newRules.length} rules...`);
        
        for (const rule of newRules) {
          await this.engine.addRule(rule);
          console.log(`✅ Added rule: ${rule.name}`);
        }
      }

      if (options.remove) {
        await this.engine.removeRule(options.remove);
        console.log(`🗑️ Removed rule: ${options.remove}`);
      }

      if (options.export) {
        const rules = this.engine.getRules();
        writeFileSync(options.export, JSON.stringify(rules, null, 2));
        console.log(`💾 Exported ${rules.length} rules to ${options.export}`);
      }

      if (options.import && existsSync(options.import)) {
        const rules: ConformanceRule[] = JSON.parse(readFileSync(options.import, 'utf-8'));
        console.log(`📥 Importing ${rules.length} rules...`);
        
        for (const rule of rules) {
          await this.engine.addRule(rule);
        }
        console.log(`✅ Successfully imported all rules`);
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Rules operation failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Handle the config command
   */
  private async handleConfigCommand(options: any): Promise<void> {
    try {
      if (options.show) {
        const config = this.engine.getConfig();
        console.log('⚙️  Current Configuration:\n');
        console.log(JSON.stringify(config, null, 2));
      }

      if (options.update && existsSync(options.update)) {
        const newConfig = JSON.parse(readFileSync(options.update, 'utf-8'));
        this.engine.updateConfig(newConfig);
        console.log(`✅ Configuration updated from ${options.update}`);
      }

      if (options.set) {
        const [key, value] = options.set.split('=', 2);
        if (key && value) {
          const updateObj = this.parseConfigValue(key, value);
          this.engine.updateConfig(updateObj);
          console.log(`✅ Set ${key} = ${value}`);
        } else {
          console.error(chalk.red('❌ Invalid format. Use: --set key=value'));
        }
      }

      if (options.export) {
        const config = this.engine.getConfig();
        writeFileSync(options.export, JSON.stringify(config, null, 2));
        console.log(`💾 Configuration exported to ${options.export}`);
      }

      if (options.reset) {
        this.config = this.loadDefaultConfig();
        this.engine.updateConfig(this.config);
        console.log('🔄 Configuration reset to defaults');
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Config operation failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Handle the metrics command
   */
  private async handleMetricsCommand(options: any): Promise<void> {
    try {
      if (options.reset) {
        this.engine.resetMetrics();
        console.log('🔄 Metrics reset');
        return;
      }

      const metrics = this.engine.getMetrics();

      if (options.format === 'table') {
        console.log('📊 Conformance Metrics\n');
        console.log('📈 Counts:');
        console.log(`   Total Verifications: ${metrics.counts.totalVerifications}`);
        console.log(`   Total Violations: ${metrics.counts.totalViolations}`);
        console.log(`   Unique Rules: ${metrics.counts.uniqueRules}`);
        console.log(`   Unique Violations: ${metrics.counts.uniqueViolations}`);
        console.log('');
        
        console.log('⚡ Performance:');
        console.log(`   Average Execution Time: ${metrics.performance.averageExecutionTime.toFixed(2)}ms`);
        console.log(`   P95 Execution Time: ${metrics.performance.p95ExecutionTime.toFixed(2)}ms`);
        console.log(`   P99 Execution Time: ${metrics.performance.p99ExecutionTime.toFixed(2)}ms`);
        console.log(`   Timeouts: ${metrics.performance.timeouts}`);
        console.log(`   Errors: ${metrics.performance.errors}`);
        console.log('');

        if (metrics.topViolations.length > 0) {
          console.log('🔝 Top Violations:');
          metrics.topViolations.slice(0, 5).forEach((violation, index) => {
            console.log(`   ${index + 1}. ${violation.ruleName} (${violation.count} times)`);
          });
        }
      } else {
        console.log(JSON.stringify(metrics, null, 2));
      }

      if (options.export) {
        writeFileSync(options.export, JSON.stringify(metrics, null, 2));
        console.log(`💾 Metrics exported to ${options.export}`);
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Metrics operation failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Handle the status command
   */
  private async handleStatusCommand(options: any): Promise<void> {
    console.log('🔧 Conformance Verification Engine Status\n');
    
    const config = this.engine.getConfig();
    const rules = this.engine.getRules();
    
    console.log(`Version: 2.2.0`);
    console.log(`Engine Mode: ${config.mode}`);
    console.log(`Enabled: ${config.enabled ? '✅' : '❌'}`);
    console.log(`Total Rules: ${rules.length}`);
    console.log(`Active Rules: ${rules.filter(r => r.enabled).length}`);
    console.log('');

    // Rule categories
    console.log('📂 Rules by Category:');
    const categories = new Map<ConformanceRuleCategory, number>();
    rules.forEach(rule => {
      categories.set(rule.category, (categories.get(rule.category) || 0) + 1);
    });

    for (const [category, count] of categories.entries()) {
      console.log(`   ${category}: ${count} rules`);
    }
    console.log('');

    // Configuration details
    console.log('⚙️  Configuration:');
    console.log(`   Mode: ${config.mode}`);
    console.log(`   Sampling: ${config.sampling?.enabled ? `${(config.sampling.rate * 100).toFixed(1)}%` : 'disabled'}`);
    console.log(`   Timeout: ${config.performance?.timeoutMs || 5000}ms`);
    console.log(`   Max Concurrent: ${config.performance?.maxConcurrentChecks || 10}`);
    console.log(`   Cache Results: ${config.performance?.cacheResults ? '✅' : '❌'}`);
    console.log('');

    if (options.monitors) {
      console.log('🔍 Active Monitors:');
      // This would show monitor-specific information
      console.log('   - Data Validation Monitor');
      console.log('   - API Contract Monitor');
      console.log('');
    }

    if (options.handlers) {
      console.log('⚡ Violation Handlers:');
      // This would show handler-specific information
      console.log('   No custom handlers configured');
      console.log('');
    }
  }

  /**
   * Handle the sample command
   */
  private async handleSampleCommand(options: any): Promise<void> {
    console.log('📝 Generating sample files...');

    // Generate sample rules
    if (options.rules) {
      const sampleRules = this.createSampleRules();
      writeFileSync(options.rules, JSON.stringify(sampleRules, null, 2));
      console.log(`📜 Sample rules generated: ${options.rules}`);
    }

    // Generate sample config
    if (options.config) {
      const sampleConfig = this.loadDefaultConfig();
      writeFileSync(options.config, JSON.stringify(sampleConfig, null, 2));
      console.log(`⚙️  Sample config generated: ${options.config}`);
    }

    // Generate sample data
    if (options.data) {
      const sampleData = this.createSampleData();
      writeFileSync(options.data, JSON.stringify(sampleData, null, 2));
      console.log(`📄 Sample data generated: ${options.data}`);
    }

    // Generate sample context
    if (options.context) {
      const sampleContext = this.createDefaultContext();
      writeFileSync(options.context, JSON.stringify(sampleContext, null, 2));
      console.log(`📋 Sample context generated: ${options.context}`);
    }

    console.log('✅ Sample files generation complete');
  }

  /**
   * Handle the report command
   */
  private async handleReportCommand(options: any): Promise<void> {
    try {
      const format = (options.format ?? 'json').toString().toLowerCase();
      if (!['json', 'markdown', 'both'].includes(format)) {
        console.error(chalk.red(`❌ Unsupported format "${options.format}". Use json, markdown, or both.`));
        safeExit(1);
        return;
      }

      const resultFiles = await this.resolveConformanceResultFiles({
        inputs: this.normalizeToArray<string>(options.inputs),
        globs: this.normalizeToArray<string>(options.glob),
        directory: typeof options.directory === 'string' ? options.directory : undefined,
        pattern: typeof options.pattern === 'string' ? options.pattern : undefined,
        useDefaults: options.defaultDiscovery !== false
      });

      if (resultFiles.length === 0) {
        console.log(chalk.yellow('⚠️  No conformance result files found. Creating empty summary.'));
      } else {
        console.log(chalk.blue(`📊 Aggregating ${resultFiles.length} conformance result file${resultFiles.length === 1 ? '' : 's'}...`));
      }

      const { runs, failedFiles } = this.loadConformanceResults(resultFiles);
      const summary = this.buildConformanceReportSummary(runs, failedFiles);

      const jsonOutput = path.resolve(typeof options.output === 'string' ? options.output : DEFAULT_REPORT_JSON);
      const markdownOutput = path.resolve(typeof options.markdownOutput === 'string' ? options.markdownOutput : DEFAULT_REPORT_MARKDOWN);

      const shouldWriteJson = format === 'json' || format === 'both';
      const shouldWriteMarkdown = format === 'markdown' || format === 'both';

      if (!shouldWriteJson && !shouldWriteMarkdown) {
        console.error(chalk.red('❌ Nothing to do. Enable JSON or Markdown output.'));
        safeExit(1);
        return;
      }

      if (shouldWriteJson) {
        this.ensureDirectoryFor(jsonOutput);
        writeFileSync(jsonOutput, JSON.stringify(summary, null, 2));
        console.log(`💾 JSON report written to ${this.toRelativePath(jsonOutput)}`);
      }

      if (shouldWriteMarkdown) {
        this.ensureDirectoryFor(markdownOutput);
        const markdown = this.renderConformanceMarkdown(summary);
        writeFileSync(markdownOutput, markdown);
        console.log(`📝 Markdown report written to ${this.toRelativePath(markdownOutput)}`);
      }

      const statusMessage =
        summary.status === 'failure'
          ? chalk.red('❌ Report generated with failing conformance runs detected.')
          : summary.status === 'success'
            ? chalk.green('✅ Conformance runs look healthy.')
            : chalk.yellow('⚠️  Conformance runs not available.');
      console.log(statusMessage);

      if (failedFiles.length > 0) {
        console.error(chalk.red(`❌ Failed to load ${failedFiles.length} conformance result file(s).`));
        failedFiles.forEach((file) => {
          console.error(chalk.red(`   - ${file}`));
        });
        safeExit(1);
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Report generation failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Display verification results
   */
  private async displayVerificationResults(result: any, options: any): Promise<void> {
    console.log('\n📊 Verification Results:\n');
    
    console.log(`✅ Overall Status: ${result.overall.toUpperCase()}`);
    console.log(`📋 Total Rules: ${result.summary.totalRules}`);
    console.log(`🔧 Rules Executed: ${result.summary.rulesExecuted}`);
    console.log(`✅ Rules Passed: ${result.summary.rulesPassed}`);
    console.log(`❌ Rules Failed: ${result.summary.rulesFailed}`);
    console.log(`⏭️  Rules Skipped: ${result.summary.rulesSkipped}`);
    console.log(`🚨 Rules Error: ${result.summary.rulesError}`);
    console.log(`⏱️  Total Duration: ${result.summary.totalDuration}ms`);
    console.log('');

    if (result.violations.length > 0) {
      console.log('🚨 Violations Found:\n');
      
      result.violations.forEach((violation: any, index: number) => {
        console.log(`${index + 1}. ${violation.ruleName}`);
        console.log(`   Category: ${violation.category}`);
        console.log(`   Severity: ${violation.severity}`);
        console.log(`   Message: ${violation.message}`);
        if (violation.actualValue !== undefined) {
          console.log(`   Actual: ${JSON.stringify(violation.actualValue)}`);
        }
        if (violation.expectedValue !== undefined) {
          console.log(`   Expected: ${JSON.stringify(violation.expectedValue)}`);
        }
        console.log('');
      });

      // Violations by severity
      console.log('📈 Violations by Severity:');
      for (const [severity, count] of Object.entries(result.summary.violationsBySeverity)) {
        if (Number(count) > 0) {
          console.log(`   ${severity}: ${count}`);
        }
      }
      console.log('');

      // Violations by category
      console.log('📂 Violations by Category:');
      for (const [category, count] of Object.entries(result.summary.violationsByCategory)) {
        if (Number(count) > 0) {
          console.log(`   ${category}: ${count}`);
        }
      }
    } else {
      console.log('🎉 No violations found - all rules passed!');
    }

    if (options.verbose && result.results) {
      console.log('\n📋 Detailed Results:\n');
      result.results.forEach((res: any, index: number) => {
        console.log(`${index + 1}. Rule ${res.ruleId}`);
        console.log(`   Status: ${res.status}`);
        console.log(`   Duration: ${res.duration}ms`);
        if (res.violation) {
          console.log(`   Violation: ${res.violation.message}`);
        }
        console.log('');
      });
    }
  }

  private normalizeToArray<T extends string>(value: T[] | T | undefined): T[] {
    if (value === undefined || value === null) {
      return [];
    }
    if (Array.isArray(value)) {
      return value.filter((item) => typeof item === 'string' && item.length > 0);
    }
    return value.length > 0 ? [value] : [];
  }

  private async resolveConformanceResultFiles(options: {
    inputs: string[];
    globs: string[];
    directory?: string;
    pattern?: string;
    useDefaults: boolean;
  }): Promise<string[]> {
    const resolved = new Set<string>();
    const missingExplicit: string[] = [];
    const patterns: string[] = [];

    for (const inputPath of options.inputs) {
      if (this.looksLikeGlob(inputPath)) {
        patterns.push(path.resolve(inputPath));
        continue;
      }

      const absolute = path.resolve(inputPath);
      if (existsSync(absolute)) {
        resolved.add(absolute);
      } else {
        missingExplicit.push(inputPath);
      }
    }

    for (const globPattern of options.globs) {
      if (globPattern.length > 0) {
        patterns.push(path.resolve(globPattern));
      }
    }

    if (options.directory) {
      const baseDir = path.resolve(options.directory);
      const derivedPattern = options.pattern ?? '*.json';
      patterns.push(path.join(baseDir, derivedPattern));
    }

    if (options.useDefaults) {
      const defaultCandidates = [
        'conformance-results.json',
        path.join('hermetic-reports', 'conformance', '*.json'),
        path.join('reports', 'conformance', '*.json')
      ];

      for (const candidate of defaultCandidates) {
        if (this.looksLikeGlob(candidate)) {
          patterns.push(path.resolve(candidate));
        } else {
          const absolute = path.resolve(candidate);
          if (existsSync(absolute)) {
            resolved.add(absolute);
          }
        }
      }
    }

    for (const patternPath of patterns) {
      const matches = await glob(patternPath, { nodir: true, absolute: true });
      for (const match of matches) {
        if (existsSync(match)) {
          resolved.add(path.resolve(match));
        }
      }
    }

    if (missingExplicit.length > 0) {
      for (const missing of missingExplicit) {
        console.warn(chalk.yellow(`⚠️  Conformance result not found: ${missing}`));
      }
    }

    return Array.from(resolved).sort();
  }

  private looksLikeGlob(value: string): boolean {
    return /[*?[\]]/.test(value);
  }

  private loadConformanceResults(files: string[]): { runs: AggregatedRunInput[]; failedFiles: string[] } {
    const runs: AggregatedRunInput[] = [];
    const failedFiles: string[] = [];

    for (const absolutePath of files) {
      try {
        const raw = readFileSync(absolutePath, 'utf-8');
        const parsed = JSON.parse(raw) as ConformanceVerificationResult;
        if (!parsed || typeof parsed !== 'object' || !parsed.summary) {
          console.warn(chalk.yellow(`⚠️  Skipping ${this.toRelativePath(absolutePath)}: missing conformance summary.`));
          continue;
        }

        const timestamp = this.resolveResultTimestamp(parsed, absolutePath);
        runs.push({
          file: this.toRelativePath(absolutePath),
          absolutePath,
          result: parsed,
          timestamp
        });
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Failed to read result ${this.toRelativePath(absolutePath)}: ${toMessage(error)}`));
        failedFiles.push(this.toRelativePath(absolutePath));
      }
    }

    return { runs, failedFiles };
  }

  private resolveResultTimestamp(result: ConformanceVerificationResult, filePath: string): string {
    if (result?.metadata?.timestamp) {
      return result.metadata.timestamp;
    }

    try {
      const stats = statSync(filePath);
      return stats.mtime.toISOString();
    } catch {
      return new Date().toISOString();
    }
  }

  private parseTimestamp(value: string): number {
    const parsed = Date.parse(value);
    return Number.isNaN(parsed) ? 0 : parsed;
  }

  private buildConformanceReportSummary(
    runs: AggregatedRunInput[],
    failedFiles: string[]
  ): ConformanceReportSummary {
    const generatedAt = new Date().toISOString();
    const statusBreakdown: Record<VerificationStatus, number> = {
      pass: 0,
      fail: 0,
      skip: 0,
      error: 0,
      timeout: 0
    };

    if (runs.length === 0) {
      const summary: ConformanceReportSummary = {
        schemaVersion: REPORT_SCHEMA_VERSION,
        generatedAt,
        status: failedFiles.length > 0 ? 'failure' : 'skipped',
        runsAnalyzed: 0,
        statusBreakdown,
        totals: {
          rulesExecuted: 0,
          rulesPassed: 0,
          rulesFailed: 0,
          rulesErrored: 0,
          rulesSkipped: 0,
          totalViolations: 0,
          uniqueRules: 0,
          uniqueViolationRules: 0
        },
        severityTotals: this.createEmptySeverityMap(),
        categoryTotals: this.createEmptyCategoryMap(),
        severityTrends: VIOLATION_SEVERITIES.map((severity) => ({
          severity,
          current: 0,
          previous: 0,
          trend: 'stable' as const
        })),
        topViolations: [],
        inputs: [],
        notes: failedFiles.length > 0
          ? `Failed to load ${failedFiles.length} conformance result file(s).`
          : 'No conformance results were discovered.'
      };

      if (failedFiles.length > 0) {
        const now = new Date().toISOString();
        failedFiles.forEach((file) => {
          statusBreakdown.error += 1;
          summary.inputs.push({
            file,
            timestamp: now,
            status: 'error',
            environment: 'unknown',
            version: 'unknown',
            totalViolations: 0
          });
        });
      }

      return summary;
    }

    const totals = {
      rulesExecuted: 0,
      rulesPassed: 0,
      rulesFailed: 0,
      rulesErrored: 0,
      rulesSkipped: 0,
      totalViolations: 0,
      uniqueRules: 0,
      uniqueViolationRules: 0
    };

    const severityTotals = this.createEmptySeverityMap();
    const categoryTotals = this.createEmptyCategoryMap();
    const uniqueRules = new Set<string>();
    const uniqueViolationRules = new Set<string>();
    const violationAccumulator = new Map<string, { ruleId: string; ruleName: string; count: number; lastObserved: string | null }>();

    const sortedRuns = [...runs].sort((a, b) => this.parseTimestamp(a.timestamp) - this.parseTimestamp(b.timestamp));
    const inputsSummary: ConformanceReportSummary['inputs'] = [];

    for (const run of sortedRuns) {
      const { result } = run;
      const overall = result.overall as VerificationStatus;
      if (overall && Object.prototype.hasOwnProperty.call(statusBreakdown, overall)) {
        statusBreakdown[overall] += 1;
      }

      totals.rulesExecuted += result.summary?.rulesExecuted ?? 0;
      totals.rulesPassed += result.summary?.rulesPassed ?? 0;
      totals.rulesFailed += result.summary?.rulesFailed ?? 0;
      totals.rulesErrored += result.summary?.rulesError ?? 0;
      totals.rulesSkipped += result.summary?.rulesSkipped ?? 0;
      totals.totalViolations += result.violations?.length ?? 0;

      for (const severity of VIOLATION_SEVERITIES) {
        const value = result.summary?.violationsBySeverity?.[severity] ?? 0;
        severityTotals[severity] += value;
      }

      for (const category of CONFORMANCE_CATEGORIES) {
        const value = result.summary?.violationsByCategory?.[category] ?? 0;
        categoryTotals[category] += value;
      }

      result.results?.forEach((res) => {
        if (res?.ruleId) {
          uniqueRules.add(res.ruleId);
        }
      });

      result.violations?.forEach((violation) => {
        if (violation.ruleId) {
          uniqueViolationRules.add(violation.ruleId);
        }

        const key = violation.ruleId ?? `${violation.ruleName}:${violation.message}`;
        if (!key) return;

        const lastObserved = this.getViolationLastObserved(violation, run.timestamp);
        const existing = violationAccumulator.get(key);
        if (existing) {
          existing.count += 1;
          if (lastObserved && (!existing.lastObserved || lastObserved > existing.lastObserved)) {
            existing.lastObserved = lastObserved;
          }
        } else {
          violationAccumulator.set(key, {
            ruleId: violation.ruleId,
            ruleName: violation.ruleName ?? violation.ruleId ?? 'unknown',
            count: 1,
            lastObserved
          });
        }
      });

    inputsSummary.push({
      file: run.file,
      timestamp: run.timestamp,
      status: overall,
      environment: result.metadata?.environment ?? 'unknown',
      version: result.metadata?.version ?? 'unknown',
      totalViolations: result.violations?.length ?? 0
    });
  }

    if (failedFiles.length > 0) {
      const now = new Date().toISOString();
      for (const failed of failedFiles) {
        statusBreakdown.error += 1;
        inputsSummary.push({
          file: failed,
          timestamp: now,
          status: 'error',
          environment: 'unknown',
          version: 'unknown',
          totalViolations: 0
        });
      }
    }

    totals.uniqueRules = uniqueRules.size;
    totals.uniqueViolationRules = uniqueViolationRules.size;

    const latestRun = sortedRuns[sortedRuns.length - 1];
    const previousRun = sortedRuns.length > 1 ? sortedRuns[sortedRuns.length - 2] : undefined;

    const severityTrends = VIOLATION_SEVERITIES.map((severity) => {
      const current = latestRun?.result.summary?.violationsBySeverity?.[severity] ?? 0;
      const previous = previousRun?.result.summary?.violationsBySeverity?.[severity] ?? 0;
      let trend: 'increasing' | 'decreasing' | 'stable' = 'stable';
      if (current > previous) {
        trend = 'increasing';
      } else if (current < previous) {
        trend = 'decreasing';
      }
      return { severity, current, previous, trend };
    });

    const status: ConformanceReportStatus =
      statusBreakdown.fail > 0 || statusBreakdown.error > 0 || statusBreakdown.timeout > 0
        ? 'failure'
        : 'success';

    const topViolations = Array.from(violationAccumulator.values())
      .sort((a, b) => {
        if (b.count !== a.count) {
          return b.count - a.count;
        }
        const aTime = a.lastObserved ? this.parseTimestamp(a.lastObserved) : 0;
        const bTime = b.lastObserved ? this.parseTimestamp(b.lastObserved) : 0;
        return bTime - aTime;
      })
      .slice(0, 10);

    const summary: ConformanceReportSummary = {
      schemaVersion: REPORT_SCHEMA_VERSION,
      generatedAt,
      status,
      runsAnalyzed: runs.length,
      statusBreakdown,
      totals,
      severityTotals,
      categoryTotals,
      severityTrends,
      topViolations,
      inputs: inputsSummary,
    };

    if (latestRun) {
      summary.latestRun = {
        file: latestRun.file,
        timestamp: latestRun.timestamp,
        status: latestRun.result.overall,
        environment: latestRun.result.metadata?.environment ?? 'unknown',
        version: latestRun.result.metadata?.version ?? 'unknown',
        rulesExecuted: latestRun.result.summary?.rulesExecuted ?? 0,
        rulesFailed: latestRun.result.summary?.rulesFailed ?? 0,
        totalViolations: latestRun.result.violations?.length ?? 0
      };
    }

    if (status === 'failure') {
      summary.notes = 'One or more runs reported failures, errors, or timeouts.';
    }

    if (failedFiles.length > 0) {
      const failureNote = `Failed to load ${failedFiles.length} conformance result file(s).`;
      summary.notes = summary.notes ? `${summary.notes} ${failureNote}` : failureNote;
    }

    return summary;
  }

  private createEmptySeverityMap(): Record<ViolationSeverity, number> {
    return VIOLATION_SEVERITIES.reduce((acc, severity) => {
      acc[severity] = 0;
      return acc;
    }, {} as Record<ViolationSeverity, number>);
  }

  private createEmptyCategoryMap(): Record<ConformanceRuleCategory, number> {
    return CONFORMANCE_CATEGORIES.reduce((acc, category) => {
      acc[category] = 0;
      return acc;
    }, {} as Record<ConformanceRuleCategory, number>);
  }

  private ensureDirectoryFor(filePath: string): void {
    const targetDir = path.dirname(filePath);
    if (!existsSync(targetDir)) {
      mkdirSync(targetDir, { recursive: true });
    }
  }

  private toRelativePath(filePath: string): string {
    const relative = path.relative(process.cwd(), filePath);
    if (!relative || relative.startsWith('..')) {
      return filePath;
    }
    return relative;
  }

  private renderConformanceMarkdown(summary: ConformanceReportSummary): string {
    const lines: string[] = [
      '# Conformance Summary',
      `- Generated: ${summary.generatedAt}`,
      `- Status: ${summary.status}`,
      `- Runs Analyzed: ${summary.runsAnalyzed}`,
      ''
    ];

    lines.push('## Totals');
    lines.push(`- Total Violations: ${summary.totals.totalViolations}`);
    lines.push(`- Rules Failed: ${summary.totals.rulesFailed}`);
    lines.push(`- Rules Passed: ${summary.totals.rulesPassed}`);
    lines.push(`- Rules Skipped: ${summary.totals.rulesSkipped}`);
    lines.push(`- Unique Rules Checked: ${summary.totals.uniqueRules}`);
    lines.push(`- Unique Violating Rules: ${summary.totals.uniqueViolationRules}`);
    lines.push('');

    lines.push('## Severity Trends');
    lines.push('| Severity | Current | Previous | Trend |');
    lines.push('| --- | --- | --- | --- |');
    for (const trend of summary.severityTrends) {
      lines.push(`| ${trend.severity} | ${trend.current} | ${trend.previous} | ${trend.trend} |`);
    }
    lines.push('');

    if (summary.topViolations.length > 0) {
      lines.push('## Top Violations');
      lines.push('| Rule | Count | Last Observed |');
      lines.push('| --- | --- | --- |');
      for (const violation of summary.topViolations) {
        lines.push(`| ${violation.ruleName || violation.ruleId} | ${violation.count} | ${violation.lastObserved ?? 'n/a'} |`);
      }
      lines.push('');
    } else {
      lines.push('## Top Violations');
      lines.push('No recurring violations detected.');
      lines.push('');
    }

    lines.push('## Runs');
    if (summary.inputs.length === 0) {
      lines.push('No conformance runs were discovered.');
    } else {
      lines.push('| File | Status | Violations | Timestamp |');
      lines.push('| --- | --- | --- | --- |');
      for (const run of summary.inputs) {
        lines.push(`| ${run.file} | ${run.status} | ${run.totalViolations} | ${run.timestamp} |`);
      }
    }

    if (summary.latestRun) {
      lines.push('');
      lines.push('## Latest Run');
      lines.push(`- File: ${summary.latestRun.file}`);
      lines.push(`- Status: ${summary.latestRun.status}`);
      lines.push(`- Environment: ${summary.latestRun.environment}`);
      lines.push(`- Version: ${summary.latestRun.version}`);
      lines.push(`- Rules Executed: ${summary.latestRun.rulesExecuted}`);
      lines.push(`- Rules Failed: ${summary.latestRun.rulesFailed}`);
      lines.push(`- Violations: ${summary.latestRun.totalViolations}`);
    }

    if (summary.notes) {
      lines.push('');
      lines.push(`_Notes_: ${summary.notes}`);
    }

    return lines.join('\n');
  }

  private getViolationLastObserved(violation: ViolationDetails, fallback: string): string | null {
    const timestamp = violation.context?.timestamp;
    if (timestamp && !Number.isNaN(Date.parse(timestamp))) {
      return timestamp;
    }
    if (fallback && !Number.isNaN(Date.parse(fallback))) {
      return fallback;
    }
    return null;
  }

  /**
   * Create default runtime context
   */
  private createDefaultContext(): RuntimeContext {
    return {
      timestamp: new Date().toISOString(),
      executionId: this.generateUUID(),
      environment: 'cli',
      version: '2.2.0',
      metadata: {
        source: 'cli',
        tool: 'conformance-cli'
      }
    };
  }

  /**
   * Load default configuration
   */
  private loadDefaultConfig(): ConformanceConfig {
    return {
      enabled: true,
      mode: 'permissive',
      rules: [],
      sampling: {
        enabled: false,
        rate: 1.0,
        strategy: 'random'
      },
      performance: {
        timeoutMs: 5000,
        maxConcurrentChecks: 10,
        cacheResults: true,
        cacheTtlMs: 300000
      },
      reporting: {
        destinations: ['console'],
        batchSize: 100,
        flushIntervalMs: 30000
      },
      alerting: {
        enabled: false,
        thresholds: {},
        channels: []
      }
    };
  }

  /**
   * Parse configuration value
   */
  private parseConfigValue(key: string, value: string): any {
    const keys = key.split('.');
    let result: any = {};
    let current = result;

    for (let i = 0; i < keys.length - 1; i++) {
      const seg = keys[i];
      if (!seg) continue;
      if (!current[seg]) current[seg] = {};
      current = current[seg];
    }

    // Parse value based on type
    let parsedValue: any = value;
    if (value === 'true') parsedValue = true;
    else if (value === 'false') parsedValue = false;
    else if (!isNaN(Number(value))) parsedValue = Number(value);

    const lastKey = keys[keys.length - 1];
    if (!lastKey) return result;
    current[lastKey] = parsedValue;
    return result;
  }

  /**
   * Create sample rules for demonstration
   */
  private createSampleRules(): ConformanceRule[] {
    const now = new Date().toISOString();
    return createEncryptedChatDefaultRules(now);
  }

  /**
   * Create sample data for testing
   */
  private createSampleData(): any {
    const now = new Date();
    const sentAt = now.toISOString();
    const receivedAt = new Date(now.getTime() + 120).toISOString();

    const userId = this.generateUUID();
    const deviceId = this.generateUUID();
    const sessionId = this.generateUUID();
    const messageId = this.generateUUID();

    return {
      user: {
        id: userId,
        displayName: 'Alice Example',
        devices: [
          {
            id: deviceId,
            platform: 'ios',
            status: 'active'
          }
        ],
        createdAt: sentAt,
        updatedAt: sentAt
      },
      device: {
        id: deviceId,
        userId,
        identityKey: 'MCowBQYDK2VuAyEAexampleIdentityKeyLzBhZVNlcg==',
        signedPreKey: 'MCowBQYDK2VuAyEAexampleSignedPreKeym9yaWdpbg==',
        preKeyStats: {
          published: 128,
          threshold: 100
        },
        platform: 'ios',
        lastSeenAt: sentAt,
        status: 'active'
      },
      session: {
        id: sessionId,
        state: 'active',
        chainKeys: ['chain-key-initial'],
        devicesActive: true,
        messagesSinceRotation: 32,
        hoursSinceRotation: 6
      },
      message: {
        id: messageId,
        sessionId,
        messageType: 'text',
        encryption: 'AES-256-GCM',
        ciphertextLength: 256,
        authTag: 'MTIzNDU2Nzg5MDEyMzQ1Ng==',
        sentAt,
        receivedAt,
        validAuthTag: true
      },
      audit: {
        appendOnly: true,
        payloadAligned: true,
        validActors: true,
        entries: [
          {
            eventType: 'device_registered',
            payload: {
              eventType: 'device_registered',
              deviceId
            }
          },
          {
            eventType: 'session_established',
            payload: {
              eventType: 'session_established',
              sessionId
            }
          }
        ]
      },
      metrics: {
        activeDeviceCount: 1,
        oneTimePreKeyCount: 128,
        deliveryLatencyMs: 240,
        gdprRetentionDays: 180,
        rotationDue: false,
        invalidAuthTagLogged: true
      }
    };
  }

  /**
   * Simple UUID generator
   */
  private generateUUID(): string {
    if (typeof randomUUID === 'function') {
      return randomUUID();
    }
    const bytes = randomBytes(16);
    bytes[6] = (bytes[6] & 0x0f) | 0x40;
    bytes[8] = (bytes[8] & 0x3f) | 0x80;
    const hex = Array.from(bytes, (b) => b.toString(16).padStart(2, '0')).join('');
    return `${hex.slice(0, 8)}-${hex.slice(8, 12)}-${hex.slice(12, 16)}-${hex.slice(16, 20)}-${hex.slice(20)}`;
  }
}

/**
 * Execute the Conformance CLI
 */
export async function executeConformanceCli(args: string[]): Promise<void> {
  const cli = new ConformanceCli();
  const command = cli.createCommand();
  
  try {
    await command.parseAsync(args);
  } catch (error: unknown) {
    console.error(chalk.red(`❌ CLI execution failed: ${toMessage(error)}`));
    safeExit(1);
  }
}
