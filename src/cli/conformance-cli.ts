/**
 * Conformance CLI Interface
 * Phase 2.2: Command-line interface for runtime conformance verification
 */

import { Command } from 'commander';
import { readFileSync, writeFileSync, existsSync } from 'fs';
import type { join } from 'path';
import { ConformanceVerificationEngine } from '../conformance/verification-engine.js';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import type { 
  ConformanceRule, 
  ConformanceConfig, 
  RuntimeContext,
  ConformanceRuleCategory,
} from '../conformance/types.js';
import type { ViolationSeverity } from '../conformance/types.js';

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
    
    return [
      {
        id: this.generateUUID(),
        name: 'Required Email Field',
        description: 'Ensures email field is present and valid',
        category: 'data_validation',
        severity: 'major',
        enabled: true,
        condition: {
          expression: 'required && email',
          variables: ['data.email'],
          constraints: {}
        },
        actions: ['log_violation'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['email', 'required', 'sample']
        }
      },
      {
        id: this.generateUUID(),
        name: 'API Response Time',
        description: 'Ensures API responses are within acceptable time limits',
        category: 'api_contract',
        severity: 'minor',
        enabled: true,
        condition: {
          expression: 'timeout',
          variables: ['data.response.time'],
          constraints: { maxMs: 1000 }
        },
        actions: ['log_violation', 'metric_increment'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['performance', 'api', 'sample']
        }
      }
    ];
  }

  /**
   * Create sample data for testing
   */
  private createSampleData(): any {
    return {
      user: {
        email: 'test@example.com',
        name: 'Test User',
        age: 25
      },
      apiCall: {
        method: 'GET',
        url: 'https://api.example.com/users/123',
        path: '/users/123',
        headers: {
          'Content-Type': 'application/json'
        },
        response: {
          status: 200,
          time: 150,
          body: { id: 123, name: 'Test User' }
        },
        timestamp: new Date().toISOString()
      }
    };
  }

  /**
   * Simple UUID generator
   */
  private generateUUID(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function(c) {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
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
