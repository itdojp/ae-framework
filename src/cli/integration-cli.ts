/**
 * Integration Testing CLI Interface
 * Phase 2.3: Command-line interface for comprehensive integration testing
 */

import { Command } from 'commander';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import chalk from 'chalk';
import { promises as fs, existsSync, statSync } from 'node:fs';
import { dirname, join } from 'path';
import { loadConfig } from '../core/config.js';
import { IntegrationTestOrchestrator } from '../integration/test-orchestrator.js';
import { E2ETestRunner } from '../integration/runners/e2e-runner.js';
import { APITestRunner } from '../integration/runners/api-runner.js';
import { HTMLTestReporter } from '../integration/reporters/html-reporter.js';
import {
  INTEGRATION_WRITE_APPROVAL_SCOPE,
  createIntegrationPathContext,
  getDefaultIntegrationOutputDir,
  isIntegrationAgentContext,
  resolveIntegrationInputPath,
  resolveIntegrationOutputPath,
  type IntegrationPathContext,
} from '../integration/path-policy.js';
import type { 
  TestCase,
  TestSuite,
  TestFixture,
  TestEnvironment,
  TestExecutionConfig,
  IntegrationTestConfig,
  TestDiscovery
} from '../integration/types.js';

const parseOptionalBoolean = (value?: string | boolean): boolean => {
  if (value === undefined) return true;
  if (typeof value === 'boolean') return value;
  const normalized = value.toLowerCase();
  return normalized === 'true' || normalized === '1' || normalized === 'yes' || normalized === 'y';
};

interface IntegrationWritePolicy {
  dryRun: boolean;
  agentContext: boolean;
  approvalRequired: boolean;
}

// Simple test discovery implementation
class FileSystemTestDiscovery implements TestDiscovery {
  constructor(private readonly pathContext: IntegrationPathContext) {}

  async discoverTests(patterns: string[]): Promise<TestCase[]> {
    const tests: TestCase[] = [];
    
    for (const pattern of patterns) {
      const resolved = resolveIntegrationInputPath(pattern, this.pathContext, 'integration test discovery path');
      if (existsSync(resolved.resolvedPath)) {
        const content = await fs.readFile(resolved.resolvedPath, 'utf-8');
        try {
          const data = JSON.parse(content);
          if (Array.isArray(data)) {
            tests.push(...data);
          } else if (data.id && data.name) {
            tests.push(data);
          }
        } catch (error) {
          console.warn(`Failed to parse test file ${resolved.workspaceRelativePath}:`, error);
        }
      }
    }
    
    return tests;
  }

  async discoverSuites(patterns: string[]): Promise<TestSuite[]> {
    const suites: TestSuite[] = [];
    
    for (const pattern of patterns) {
      const resolved = resolveIntegrationInputPath(pattern, this.pathContext, 'integration suite discovery path');
      if (existsSync(resolved.resolvedPath)) {
        const content = await fs.readFile(resolved.resolvedPath, 'utf-8');
        try {
          const data = JSON.parse(content);
          if (Array.isArray(data)) {
            suites.push(...data);
          } else if (data.id && data.name && data.tests) {
            suites.push(data);
          }
        } catch (error) {
          console.warn(`Failed to parse suite file ${resolved.workspaceRelativePath}:`, error);
        }
      }
    }
    
    return suites;
  }

  async discoverFixtures(patterns: string[]): Promise<TestFixture[]> {
    const fixtures: TestFixture[] = [];
    
    for (const pattern of patterns) {
      const resolved = resolveIntegrationInputPath(pattern, this.pathContext, 'integration fixture discovery path');
      if (existsSync(resolved.resolvedPath)) {
        const content = await fs.readFile(resolved.resolvedPath, 'utf-8');
        try {
          const data = JSON.parse(content);
          if (Array.isArray(data)) {
            fixtures.push(...data);
          } else if (data.id && data.name) {
            fixtures.push(data);
          }
        } catch (error) {
          console.warn(`Failed to parse fixtures file ${resolved.workspaceRelativePath}:`, error);
        }
      }
    }
    
    return fixtures;
  }
}

export class IntegrationTestingCli {
  private orchestrator: IntegrationTestOrchestrator;
  private discovery: TestDiscovery;
  private pathContext: IntegrationPathContext;

  constructor() {
    this.pathContext = createIntegrationPathContext();
    // Default configuration
    const config: IntegrationTestConfig = {
      environments: [this.createDefaultEnvironment()],
      defaultEnvironment: 'default',
      runners: [
        new E2ETestRunner({
          browser: 'chromium',
          headless: true,
          viewport: { width: 1280, height: 720 },
          timeout: 30000,
          retries: 1,
          screenshots: true,
          video: false,
          trace: false,
          slowMo: 0,
          outputDir: this.getDefaultOutputDir()
        }),
        new APITestRunner({
          timeout: 10000,
          retries: 2,
          validateSchema: true,
          followRedirects: true,
          validateSSL: true,
          maxResponseSize: 10 * 1024 * 1024, // 10MB
          defaultHeaders: {
            'User-Agent': 'AE-Framework-Integration-Tests/1.0'
          }
        })
      ],
      reporters: [
        new HTMLTestReporter()
      ],
      globalTimeout: 600000, // 10 minutes
      globalRetries: 1,
      parallelSuites: false,
      maxSuiteConcurrency: 2,
      artifactRetention: {
        days: 30,
        maxSize: 1000 // 1GB
      },
      notifications: {
        enabled: false,
        channels: [],
        onFailure: true,
        onSuccess: false
      }
    };

    this.orchestrator = new IntegrationTestOrchestrator(config);
    this.discovery = new FileSystemTestDiscovery(this.pathContext);
  }

  /**
   * Create and configure the CLI command
   */
  createCommand(): Command {
    const command = new Command('integration')
      .description('Comprehensive integration testing system')
      .version('2.3.0');

    // Run command - execute tests
    command
      .command('run')
      .description('Execute integration tests')
      .option('-s, --suites <patterns>', 'Test suite patterns (comma-separated)', '')
      .option('-t, --tests <patterns>', 'Test case patterns (comma-separated)', '')
      .option('-e, --environment <name>', 'Test environment', 'default')
      .option('-p, --parallel [boolean]', 'Run tests in parallel', parseOptionalBoolean)
      .option('--max-concurrency <num>', 'Maximum parallel tests', (value) => parseInt(value, 10))
      .option('--timeout <ms>', 'Global timeout in milliseconds', '600000')
      .option('--retries <num>', 'Number of retries for failed tests', '1')
      .option('--fail-fast', 'Stop execution on first failure')
      .option('--skip-on-failure', 'Skip remaining tests on failure')
      .option('--output-dir <dir>', 'Output directory for results', this.getDefaultOutputDir())
      .option('--report-format <formats>', 'Report formats (comma-separated)', 'html,json')
      .option('--categories <categories>', 'Test categories to run (comma-separated)')
      .option('--tags <tags>', 'Test tags to run (comma-separated)')
      .option('--exclude <tests>', 'Test IDs to exclude (comma-separated)')
      .option('--screenshots', 'Capture screenshots on failures')
      .option('--video', 'Record video of test execution')
      .option('--coverage', 'Measure code coverage')
      .option('--dry-run', 'Preview write-capable integration execution without writing artifacts')
      .option('--apply', 'Apply write-capable integration execution in an agent context')
      .option('--approval-scope <scope>', `Trusted write approval scope (${INTEGRATION_WRITE_APPROVAL_SCOPE})`)
      .action(async (options) => {
        await this.handleRunCommand(options);
      });

    // Discover command - find available tests
    command
      .command('discover')
      .description('Discover available tests, suites, and fixtures')
      .option('-p, --patterns <patterns>', 'File patterns to search (comma-separated)', './tests/**/*.json')
      .option('-t, --type <type>', 'Discovery type (tests, suites, fixtures, all)', 'all')
      .option('-o, --output <file>', 'Output file for discovered items')
      .option('--format <format>', 'Output format (json, table)', 'table')
      .option('--dry-run', 'Preview discovery output writes without writing files')
      .option('--apply', 'Apply discovery output writes in an agent context')
      .option('--approval-scope <scope>', `Trusted write approval scope (${INTEGRATION_WRITE_APPROVAL_SCOPE})`)
      .action(async (options) => {
        await this.handleDiscoverCommand(options);
      });

    // List command - show available environments, runners, etc.
    command
      .command('list')
      .description('List available resources')
      .option('-t, --type <type>', 'Resource type (environments, runners, reporters)', 'environments')
      .action(async (options) => {
        await this.handleListCommand(options);
      });

    // Generate command - create sample test configurations
    command
      .command('generate')
      .description('Generate sample test configurations')
      .option('-t, --type <type>', 'Generation type (test, suite, fixture, environment)', 'test')
      .option('-o, --output <file>', 'Output file')
      .option('--test-type <testType>', 'Test type for generation (e2e, api, unit)', 'e2e')
      .option('--name <name>', 'Name for generated item', 'Sample Test')
      .option('--dry-run', 'Preview generated output without writing files')
      .option('--apply', 'Apply generated output writes in an agent context')
      .option('--approval-scope <scope>', `Trusted write approval scope (${INTEGRATION_WRITE_APPROVAL_SCOPE})`)
      .action(async (options) => {
        await this.handleGenerateCommand(options);
      });

    // Status command - show execution status
    command
      .command('status')
      .description('Show current test execution status')
      .option('-w, --watch', 'Watch for status changes')
      .option('--refresh <seconds>', 'Refresh interval for watch mode', '5')
      .action(async (options) => {
        await this.handleStatusCommand(options);
      });

    // Reports command - manage test reports
    command
      .command('reports')
      .description('Manage and view test reports')
      .option('-l, --list', 'List available reports')
      .option('-v, --view <reportId>', 'View specific report')
      .option('-c, --clean', 'Clean old reports')
      .option('--days <days>', 'Report retention days', '30')
      .option('--dry-run', 'Preview report cleanup without deleting files')
      .option('--apply', 'Apply report cleanup in an agent context')
      .option('--approval-scope <scope>', `Trusted write approval scope (${INTEGRATION_WRITE_APPROVAL_SCOPE})`)
      .action(async (options) => {
        await this.handleReportsCommand(options);
      });

    return command;
  }

  /**
   * Handle the run command
   */
  private async handleRunCommand(options: any): Promise<void> {
    try {
      const cfg = await loadConfig();
      const mode = cfg.mode ?? 'copilot';
      const writePolicy = this.getWritePolicy(options);
      console.log('🚀 Starting integration test execution...');

      // Parse patterns
      const suitePatterns = this.parsePathList(options.suites);
      const testPatterns = this.parsePathList(options.tests);
      const allPatterns = [...suitePatterns, ...testPatterns];

      if (allPatterns.length === 0) {
        // Default patterns
        allPatterns.push('tests/**/*.json', 'tests/**/*.test.json');
      }
      const safePatterns = allPatterns.map((pattern) =>
        resolveIntegrationInputPath(pattern, this.pathContext, 'integration test pattern').workspaceRelativePath
      );
      const outputDir = resolveIntegrationOutputPath(
        options.outputDir,
        this.pathContext,
        'integration output directory',
      ).workspaceRelativePath;

      if (writePolicy.approvalRequired) {
        console.error(chalk.red(`❌ Integration writes require --approval-scope ${INTEGRATION_WRITE_APPROVAL_SCOPE} when --apply is used in an agent context`));
        safeExit(1);
        return;
      }

      if (writePolicy.dryRun) {
        console.log('🔎 Dry-run preview: no tests will be executed and no integration artifacts will be written.');
        console.log(`   Read patterns: ${safePatterns.join(', ')}`);
        console.log(`   Planned output directory: ${outputDir}`);
        return;
      }

      // Initialize orchestrator only after path policy and write approval checks pass.
      await this.orchestrator.initialize();

      // Discover tests
      console.log('🔍 Discovering tests...');
      const discovered = await this.orchestrator.discoverTests(this.discovery, safePatterns);
      
      console.log(`📋 Found ${discovered.tests.length} tests, ${discovered.suites.length} suites, ${discovered.fixtures.length} fixtures`);

      if (discovered.tests.length === 0 && discovered.suites.length === 0) {
        console.log('⚠️  No tests or suites found. Use --patterns to specify test locations.');
        return;
      }

      // Create execution configuration
      const parallel = typeof options.parallel === 'boolean'
        ? options.parallel
        : mode === 'delegated';
      const maxConcurrency = Number.isFinite(options.maxConcurrency)
        ? options.maxConcurrency
        : parallel
          ? 4
          : 1;

      const config: TestExecutionConfig = {
        environment: options.environment,
        parallel,
        maxConcurrency,
        timeout: parseInt(options.timeout, 10) || 600000,
        retries: parseInt(options.retries, 10),
        skipOnFailure: options.skipOnFailure || false,
        failFast: options.failFast || false,
        generateReport: true,
        captureScreenshots: options.screenshots || false,
        recordVideo: options.video || false,
        collectLogs: true,
        measureCoverage: options.coverage || false,
        outputDir,
        reportFormat: options.reportFormat.split(',').map((f: string) => f.trim()),
        filters: {
          categories: options.categories ? options.categories.split(',').map((c: string) => c.trim()) : undefined,
          tags: options.tags ? options.tags.split(',').map((t: string) => t.trim()) : undefined,
          exclude: options.exclude ? options.exclude.split(',').map((e: string) => e.trim()) : undefined
        }
      };

      let totalResults: any[] = [];
      
      // Execute test suites
      for (const suite of discovered.suites) {
        console.log(`\n📦 Executing suite: ${suite.name}`);
        
        try {
          const summary = await this.orchestrator.executeSuite(suite.id, options.environment, config);
          totalResults.push(summary);
          
          const passRate = summary.statistics.passRate;
          const status = passRate >= 80 ? '✅' : passRate >= 60 ? '⚠️' : '❌';
          
          console.log(`${status} Suite completed: ${summary.statistics.passed}/${summary.statistics.total} passed (${passRate.toFixed(1)}%)`);
          
          if (config.failFast && summary.statistics.failed > 0) {
            console.log('🛑 Stopping execution due to --fail-fast flag');
            break;
          }
          
        } catch (error: unknown) {
            console.error(chalk.red(`❌ Suite execution failed: ${toMessage(error)}`));
          
          if (config.failFast) {
            throw error;
          }
        }
      }

      // Execute individual tests if no suites
      if (discovered.suites.length === 0) {
        for (const test of discovered.tests) {
          console.log(`\n🧪 Executing test: ${test.name}`);
          
          try {
            const result = await this.orchestrator.executeTest(test.id, options.environment, config);
            console.log(`${result.status === 'passed' ? '✅' : '❌'} Test ${result.status}: ${test.name} (${result.duration}ms)`);
            
            if (config.failFast && result.status === 'failed') {
              console.log('🛑 Stopping execution due to --fail-fast flag');
              break;
            }
            
          } catch (error: unknown) {
            console.error(chalk.red(`❌ Test execution failed: ${toMessage(error)}`));
            
            if (config.failFast) {
              throw error;
            }
          }
        }
      }

      // Final summary
      if (totalResults.length > 0) {
        const totalPassed = totalResults.reduce((sum, result) => sum + result.statistics.passed, 0);
        const totalTests = totalResults.reduce((sum, result) => sum + result.statistics.total, 0);
        const overallPassRate = totalTests > 0 ? (totalPassed / totalTests) * 100 : 0;
        
        console.log('\n📊 Overall Summary:');
        console.log(`   Total Tests: ${totalTests}`);
        console.log(`   Passed: ${totalPassed}`);
        console.log(`   Pass Rate: ${overallPassRate.toFixed(1)}%`);
        
        if (overallPassRate < 100) {
          console.log(`\n💡 Check the generated reports in ${config.outputDir} for detailed failure analysis.`);
        }
      }

      console.log('✅ Integration test execution completed');

    } catch (error) {
            console.error(chalk.red(`❌ Integration test execution failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Handle the discover command
   */
  private async handleDiscoverCommand(options: any): Promise<void> {
    try {
      const writePolicy = this.getWritePolicy(options);
      console.log('🔍 Discovering test resources...');

      const patterns = this.parsePathList(options.patterns).map((pattern) =>
        resolveIntegrationInputPath(pattern, this.pathContext, 'integration discovery pattern').workspaceRelativePath
      );
      const outputPath = options.output
        ? resolveIntegrationOutputPath(options.output, this.pathContext, 'integration discovery output').workspaceRelativePath
        : undefined;
      
      let items: any = [];
      let itemType = '';

      switch (options.type) {
        case 'tests':
          items = await this.discovery.discoverTests(patterns);
          itemType = 'tests';
          break;
        case 'suites':
          items = await this.discovery.discoverSuites(patterns);
          itemType = 'suites';
          break;
        case 'fixtures':
          items = await this.discovery.discoverFixtures(patterns);
          itemType = 'fixtures';
          break;
        case 'all':
          const [tests, suites, fixtures] = await Promise.all([
            this.discovery.discoverTests(patterns),
            this.discovery.discoverSuites(patterns),
            this.discovery.discoverFixtures(patterns)
          ]);
          items = { tests, suites, fixtures };
          itemType = 'all';
          break;
        default:
          throw new Error(`Unknown discovery type: ${options.type}`);
      }

      if (options.format === 'table') {
        this.displayDiscoveryTable(items, itemType);
      } else {
        console.log(JSON.stringify(items, null, 2));
      }

      if (outputPath) {
        if (writePolicy.approvalRequired) {
          console.error(chalk.red(`❌ Integration discovery output writes require --approval-scope ${INTEGRATION_WRITE_APPROVAL_SCOPE} when --apply is used in an agent context`));
          safeExit(1);
          return;
        }
        if (writePolicy.dryRun) {
          console.log(`🔎 Dry-run preview: discovery results would be saved to ${outputPath}`);
          return;
        }
        const resolvedOutput = resolveIntegrationOutputPath(
          outputPath,
          this.pathContext,
          'integration discovery output',
        ).resolvedPath;
        await fs.mkdir(dirname(resolvedOutput), { recursive: true });
        await fs.writeFile(resolvedOutput, JSON.stringify(items, null, 2));
        console.log(`💾 Results saved to ${outputPath}`);
      }

    } catch (error) {
            console.error(chalk.red(`❌ Discovery failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Handle the list command
   */
  private async handleListCommand(options: any): Promise<void> {
    console.log(`📋 Available ${options.type}:\n`);

    switch (options.type) {
      case 'environments':
        const environments = this.orchestrator.getEnvironments();
        environments.forEach((env, index) => {
          console.log(`${index + 1}. ${env.name}`);
          if (env.baseUrl) console.log(`   Base URL: ${env.baseUrl}`);
          if (env.apiUrl) console.log(`   API URL: ${env.apiUrl}`);
          console.log(`   Variables: ${Object.keys(env.variables).length}`);
          console.log('');
        });
        break;

      case 'runners':
        const runners = this.orchestrator.getRunners();
        runners.forEach((runner, index) => {
          console.log(`${index + 1}. ${runner.name} (${runner.id})`);
          console.log(`   Category: ${runner.category}`);
          console.log('');
        });
        break;

      case 'reporters':
        // Would list available reporters
        console.log('1. HTML Reporter (html)');
        console.log('   Generates comprehensive HTML reports with charts and filtering');
        console.log('');
        break;

      default:
        console.error(chalk.red(`❌ Unknown resource type: ${options.type}`));
        safeExit(1);
    }
  }

  /**
   * Handle the generate command
   */
  private async handleGenerateCommand(options: any): Promise<void> {
    try {
      const writePolicy = this.getWritePolicy(options);
      console.log(`🛠️ Generating sample ${options.type}...`);

      let generatedItem: any;

      switch (options.type) {
        case 'test':
          generatedItem = this.generateSampleTest(options);
          break;
        case 'suite':
          generatedItem = this.generateSampleSuite(options);
          break;
        case 'fixture':
          generatedItem = this.generateSampleFixture(options);
          break;
        case 'environment':
          generatedItem = this.generateSampleEnvironment(options);
          break;
        default:
          throw new Error(`Unknown generation type: ${options.type}`);
      }

      if (options.output) {
        const outputPath = resolveIntegrationOutputPath(
          options.output,
          this.pathContext,
          'integration generated output',
        );
        if (writePolicy.approvalRequired) {
          console.error(chalk.red(`❌ Integration generated output writes require --approval-scope ${INTEGRATION_WRITE_APPROVAL_SCOPE} when --apply is used in an agent context`));
          safeExit(1);
          return;
        }
        if (writePolicy.dryRun) {
          console.log(`🔎 Dry-run preview: generated ${options.type} would be saved to ${outputPath.workspaceRelativePath}`);
          return;
        }
        await fs.mkdir(dirname(outputPath.resolvedPath), { recursive: true });
        await fs.writeFile(outputPath.resolvedPath, JSON.stringify(generatedItem, null, 2));
        console.log(`✅ Generated ${options.type} saved to ${outputPath.workspaceRelativePath}`);
      } else {
        console.log(JSON.stringify(generatedItem, null, 2));
      }

    } catch (error) {
            console.error(chalk.red(`❌ Generation failed: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Handle the status command
   */
  private async handleStatusCommand(options: any): Promise<void> {
    if (options.watch) {
      console.log('👀 Watching test execution status... (Press Ctrl+C to exit)');
      
      const refreshInterval = parseInt(options.refresh) * 1000;
      const showStatus = () => {
        console.clear();
        console.log('🔄 Test Execution Status');
        console.log('========================\n');
        
        // In a real implementation, would show actual execution status
        console.log('Current Executions: 0');
        console.log('Queue Length: 0');
        console.log('Last Update:', new Date().toLocaleString());
        console.log('\n(No active executions)');
      };

      showStatus();
      setInterval(showStatus, refreshInterval);
      
    } else {
      console.log('📊 Integration Testing System Status\n');
      console.log('Orchestrator: Ready');
      console.log('Environments: ' + this.orchestrator.getEnvironments().length);
      console.log('Runners: ' + this.orchestrator.getRunners().length);
      console.log('Active Executions: 0');
    }
  }

  /**
   * Handle the reports command
   */
  private async handleReportsCommand(options: any): Promise<void> {
    const writePolicy = this.getWritePolicy(options);
    const reportsDir = resolveIntegrationOutputPath(
      this.getDefaultOutputDir(),
      this.pathContext,
      'integration reports directory',
    );

    if (options.list) {
      console.log('📄 Available Test Reports:\n');
      
      try {
        if (existsSync(reportsDir.resolvedPath)) {
          const files = await fs.readdir(reportsDir.resolvedPath);
          const reportFiles = files.filter(f => f.endsWith('.html') || f.endsWith('.json'));
          
          if (reportFiles.length === 0) {
            console.log('No reports found in the reports directory. Run tests to generate reports.');
          } else {
            reportFiles.forEach((file, index) => {
              console.log(`${index + 1}. ${file}`);
              const filePath = join(reportsDir.resolvedPath, file);
              if (existsSync(filePath)) {
                const stats = statSync(filePath);
                console.log(`   Created: ${stats.ctime.toLocaleString()}`);
                console.log(`   Size: ${this.formatFileSize(stats.size)}`);
              }
              console.log('');
            });
          }
        } else {
          console.log('No reports found in the reports directory. Run tests to generate reports.');
        }
      } catch (error) {
                console.error(chalk.red(`❌ Failed to list reports: ${toMessage(error)}`));
      }
    }

    if (options.clean) {
      console.log('🧹 Cleaning old reports...');
      if (writePolicy.approvalRequired) {
        console.error(chalk.red(`❌ Integration report cleanup requires --approval-scope ${INTEGRATION_WRITE_APPROVAL_SCOPE} when --apply is used in an agent context`));
        safeExit(1);
        return;
      }
      
      const retentionDays = parseInt(options.days);
      const cutoffDate = new Date(Date.now() - retentionDays * 24 * 60 * 60 * 1000);
      
      try {
        if (existsSync(reportsDir.resolvedPath)) {
          const files = await fs.readdir(reportsDir.resolvedPath);
          let cleaned = 0;
          
          for (const file of files) {
            const filePath = join(reportsDir.resolvedPath, file);
            const stats = statSync(filePath);
            
            if (stats.ctime < cutoffDate) {
              if (!writePolicy.dryRun) {
                await fs.unlink(filePath);
              }
              cleaned++;
            }
          }
          
          if (writePolicy.dryRun) {
            console.log(`🔎 Dry-run preview: would clean ${cleaned} old reports (older than ${retentionDays} days)`);
          } else {
            console.log(`✅ Cleaned ${cleaned} old reports (older than ${retentionDays} days)`);
          }
        }
      } catch (error) {
                console.error(chalk.red(`❌ Failed to clean reports: ${toMessage(error)}`));
      }
    }
  }

  private parsePathList(value?: string): string[] {
    if (!value) return [];
    return value
      .split(',')
      .map((item: string) => item.trim())
      .filter((item: string) => item.length > 0);
  }

  private getWritePolicy(options: any): IntegrationWritePolicy {
    const agentContext = isIntegrationAgentContext();
    const applyRequested = options.apply === true;
    const approved = options.approvalScope === INTEGRATION_WRITE_APPROVAL_SCOPE;
    const approvalRequired = agentContext && applyRequested && !approved;
    const dryRun = options.dryRun === true || (agentContext && !applyRequested);
    return {
      dryRun,
      agentContext,
      approvalRequired,
    };
  }

  private getDefaultOutputDir(): string {
    return getDefaultIntegrationOutputDir(this.pathContext);
  }

  /**
   * Create default environment
   */
  private createDefaultEnvironment(): TestEnvironment {
    return {
      name: 'default',
      baseUrl: 'http://localhost:3000',
      apiUrl: 'http://localhost:3000/api',
      variables: {
        API_KEY: 'test-api-key',
        API_TOKEN: 'test-token'
      },
      timeouts: {
        default: 30000,
        api: 10000,
        ui: 5000,
        database: 15000
      },
      retries: {
        max: 3,
        delay: 1000
      }
    };
  }

  /**
   * Display discovery results in table format
   */
  private displayDiscoveryTable(items: any, itemType: string): void {
    if (itemType === 'all') {
      console.log('📊 Discovery Summary:');
      console.log(`   Tests: ${items.tests.length}`);
      console.log(`   Suites: ${items.suites.length}`);
      console.log(`   Fixtures: ${items.fixtures.length}\n`);
      
      if (items.tests.length > 0) {
        console.log('🧪 Tests:');
        items.tests.forEach((test: TestCase, index: number) => {
          console.log(`   ${index + 1}. ${test.name} (${test.category}, ${test.severity})`);
        });
        console.log('');
      }
      
      if (items.suites.length > 0) {
        console.log('📦 Suites:');
        items.suites.forEach((suite: TestSuite, index: number) => {
          console.log(`   ${index + 1}. ${suite.name} (${suite.tests.length} tests)`);
        });
        console.log('');
      }
      
    } else {
      console.log(`📋 Found ${items.length} ${itemType}:`);
      items.forEach((item: any, index: number) => {
        console.log(`   ${index + 1}. ${item.name} (${item.id})`);
      });
      console.log('');
    }
  }

  /**
   * Generate sample test case
   */
  private generateSampleTest(options: any): TestCase {
    const now = new Date().toISOString();
    
    return {
      id: 'sample-test-' + Date.now(),
      name: options.name || 'Sample E2E Test',
      description: 'A sample end-to-end test case generated by the CLI',
      category: options.testType === 'api' ? 'integration' : 'e2e',
      severity: 'major',
      enabled: true,
      preconditions: [
        'Application server is running',
        'Test data is available'
      ],
      steps: options.testType === 'api' ? [
        {
          id: 'step-1',
          description: 'Make GET request to API',
          action: 'api:request:GET:/health',
          data: {},
          expectedResult: 'Returns 200 OK status'
        },
        {
          id: 'step-2', 
          description: 'Validate response',
          action: 'api:validate:status:200',
          data: {},
          expectedResult: 'Status code is 200'
        }
      ] : [
        {
          id: 'step-1',
          description: 'Navigate to home page',
          action: 'navigate:/',
          data: {},
          expectedResult: 'Page loads successfully'
        },
        {
          id: 'step-2',
          description: 'Click login button',
          action: 'click:button[data-testid="login-btn"]',
          data: {},
          expectedResult: 'Login modal appears'
        },
        {
          id: 'step-3',
          description: 'Verify page title',
          action: 'verify:text:h1:Welcome',
          data: {
            validation: {
              type: 'text',
              expected: 'Welcome'
            }
          },
          expectedResult: 'Page title contains Welcome'
        }
      ],
      expectedResults: [
        'User can successfully navigate the application',
        'All interactions work as expected'
      ],
      fixtures: [],
      dependencies: [],
      tags: ['sample', 'generated'],
      metadata: {
        estimatedDuration: 30000,
        complexity: 'medium',
        stability: 'stable',
        lastUpdated: now
      }
    };
  }

  /**
   * Generate sample test suite
   */
  private generateSampleSuite(options: any): TestSuite {
    return {
      id: 'sample-suite-' + Date.now(),
      name: options.name || 'Sample Test Suite',
      description: 'A sample test suite generated by the CLI',
      category: 'e2e',
      tests: [], // Would be populated with actual test IDs
      fixtures: [],
      configuration: {
        parallel: false,
        maxConcurrency: 1,
        timeout: 300000,
        retries: 1,
        skipOnFailure: false,
        failFast: false
      },
      setup: ['shell:npm start'],
      teardown: ['shell:npm stop'],
      metadata: {
        estimatedDuration: 180000,
        priority: 'medium',
        tags: ['sample', 'generated']
      }
    };
  }

  /**
   * Generate sample fixture
   */
  private generateSampleFixture(options: any): TestFixture {
    const now = new Date().toISOString();
    
    return {
      id: 'sample-fixture-' + Date.now(),
      name: options.name || 'Sample Test Fixture',
      description: 'A sample test fixture generated by the CLI',
      category: 'unit',
      data: {
        users: [
          { id: 1, name: 'Test User 1', email: 'user1@test.com' },
          { id: 2, name: 'Test User 2', email: 'user2@test.com' }
        ],
        config: {
          apiTimeout: 5000,
          retryCount: 3
        }
      },
      setup: ['sql:INSERT INTO users (name, email) VALUES ("Test User", "test@example.com")'],
      teardown: ['sql:DELETE FROM users WHERE email LIKE "%@test.com"'],
      dependencies: [],
      metadata: {
        createdAt: now,
        updatedAt: now,
        version: '1.0.0',
        tags: ['sample', 'generated']
      }
    };
  }

  /**
   * Generate sample environment
   */
  private generateSampleEnvironment(options: any): TestEnvironment {
    return {
      name: options.name || 'sample-env',
      baseUrl: 'http://localhost:3000',
      apiUrl: 'http://localhost:3000/api',
      database: {
        host: 'localhost',
        port: 5432,
        name: 'test_db',
        username: 'test_user'
      },
      variables: {
        API_KEY: 'sample-api-key',
        DATABASE_URL: 'postgresql://localhost:5432/test_db'
      },
      timeouts: {
        default: 30000,
        api: 10000,
        ui: 5000,
        database: 15000
      },
      retries: {
        max: 3,
        delay: 1000
      }
    };
  }

  /**
   * Format file size
   */
  private formatFileSize(bytes: number): string {
    const sizes = ['B', 'KB', 'MB', 'GB'];
    if (bytes === 0) return '0 B';
    
    const i = Math.floor(Math.log(bytes) / Math.log(1024));
    return `${(bytes / Math.pow(1024, i)).toFixed(1)} ${sizes[i]}`;
  }
}

/**
 * Execute the Integration Testing CLI
 */
export async function executeIntegrationCli(args: string[]): Promise<void> {
  const cli = new IntegrationTestingCli();
  const command = cli.createCommand();
  
  try {
    await command.parseAsync(args);
  } catch (error) {
        console.error(chalk.red(`❌ CLI execution failed: ${toMessage(error)}`));
    safeExit(1);
  }
}
