/**
 * Integration Testing CLI Interface
 * Phase 2.3: Command-line interface for comprehensive integration testing
 */

import { Command } from 'commander';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import chalk from 'chalk';
import { promises as fs } from 'fs';
import { join, resolve } from 'path';
import { existsSync } from 'fs';
import { IntegrationTestOrchestrator } from '../integration/test-orchestrator.js';
import { E2ETestRunner } from '../integration/runners/e2e-runner.js';
import { APITestRunner } from '../integration/runners/api-runner.js';
import { HTMLTestReporter } from '../integration/reporters/html-reporter.js';
import type { 
  TestCase,
  TestSuite,
  TestFixture,
  TestEnvironment,
  TestExecutionConfig,
  IntegrationTestConfig,
  TestDiscovery
} from '../integration/types.js';

// Simple test discovery implementation
class FileSystemTestDiscovery implements TestDiscovery {
  async discoverTests(patterns: string[]): Promise<TestCase[]> {
    const tests: TestCase[] = [];
    
    for (const pattern of patterns) {
      if (existsSync(pattern)) {
        const content = await fs.readFile(pattern, 'utf-8');
        try {
          const data = JSON.parse(content);
          if (Array.isArray(data)) {
            tests.push(...data);
          } else if (data.id && data.name) {
            tests.push(data);
          }
        } catch (error) {
          console.warn(`Failed to parse test file ${pattern}:`, error);
        }
      }
    }
    
    return tests;
  }

  async discoverSuites(patterns: string[]): Promise<TestSuite[]> {
    const suites: TestSuite[] = [];
    
    for (const pattern of patterns) {
      if (existsSync(pattern)) {
        const content = await fs.readFile(pattern, 'utf-8');
        try {
          const data = JSON.parse(content);
          if (Array.isArray(data)) {
            suites.push(...data);
          } else if (data.id && data.name && data.tests) {
            suites.push(data);
          }
        } catch (error) {
          console.warn(`Failed to parse suite file ${pattern}:`, error);
        }
      }
    }
    
    return suites;
  }

  async discoverFixtures(patterns: string[]): Promise<TestFixture[]> {
    const fixtures: TestFixture[] = [];
    
    for (const pattern of patterns) {
      if (existsSync(pattern)) {
        const content = await fs.readFile(pattern, 'utf-8');
        try {
          const data = JSON.parse(content);
          if (Array.isArray(data)) {
            fixtures.push(...data);
          } else if (data.id && data.name) {
            fixtures.push(data);
          }
        } catch (error) {
          console.warn(`Failed to parse fixtures file ${pattern}:`, error);
        }
      }
    }
    
    return fixtures;
  }
}

export class IntegrationTestingCli {
  private orchestrator: IntegrationTestOrchestrator;
  private discovery: TestDiscovery;

  constructor() {
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
          slowMo: 0
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
    this.discovery = new FileSystemTestDiscovery();
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
      .option('-p, --parallel', 'Run tests in parallel')
      .option('--max-concurrency <num>', 'Maximum parallel tests', '4')
      .option('--timeout <ms>', 'Global timeout in milliseconds', '600000')
      .option('--retries <num>', 'Number of retries for failed tests', '1')
      .option('--fail-fast', 'Stop execution on first failure')
      .option('--skip-on-failure', 'Skip remaining tests on failure')
      .option('--output-dir <dir>', 'Output directory for results', './test-results')
      .option('--report-format <formats>', 'Report formats (comma-separated)', 'html,json')
      .option('--categories <categories>', 'Test categories to run (comma-separated)')
      .option('--tags <tags>', 'Test tags to run (comma-separated)')
      .option('--exclude <tests>', 'Test IDs to exclude (comma-separated)')
      .option('--screenshots', 'Capture screenshots on failures')
      .option('--video', 'Record video of test execution')
      .option('--coverage', 'Measure code coverage')
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
      console.log('🚀 Starting integration test execution...');

      // Initialize orchestrator
      await this.orchestrator.initialize();

      // Parse patterns
      const suitePatterns = options.suites ? options.suites.split(',').map((s: string) => s.trim()) : [];
      const testPatterns = options.tests ? options.tests.split(',').map((s: string) => s.trim()) : [];
      const allPatterns = [...suitePatterns, ...testPatterns];

      if (allPatterns.length === 0) {
        // Default patterns
        allPatterns.push('./tests/**/*.json', './tests/**/*.test.json');
      }

      // Discover tests
      console.log('🔍 Discovering tests...');
      const discovered = await this.orchestrator.discoverTests(this.discovery, allPatterns);
      
      console.log(`📋 Found ${discovered.tests.length} tests, ${discovered.suites.length} suites, ${discovered.fixtures.length} fixtures`);

      if (discovered.tests.length === 0 && discovered.suites.length === 0) {
        console.log('⚠️  No tests or suites found. Use --patterns to specify test locations.');
        return;
      }

      // Create execution configuration
      const config: TestExecutionConfig = {
        environment: options.environment,
        parallel: options.parallel || false,
        maxConcurrency: parseInt(options.maxConcurrency),
        timeout: parseInt(options.timeout),
        retries: parseInt(options.retries),
        skipOnFailure: options.skipOnFailure || false,
        failFast: options.failFast || false,
        generateReport: true,
        captureScreenshots: options.screenshots || false,
        recordVideo: options.video || false,
        collectLogs: true,
        measureCoverage: options.coverage || false,
        outputDir: options.outputDir,
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
      console.log('🔍 Discovering test resources...');

      const patterns = options.patterns.split(',').map((p: string) => p.trim());
      
      let items: any[] = [];
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
    // items = { tests, suites, fixtures }; // TODO: Verify property exists in interface
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

      if (options.output) {
        await fs.writeFile(options.output, JSON.stringify(items, null, 2));
        console.log(`💾 Results saved to ${options.output}`);
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
        await fs.writeFile(options.output, JSON.stringify(generatedItem, null, 2));
        console.log(`✅ Generated ${options.type} saved to ${options.output}`);
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
    const reportsDir = './test-results';

    if (options.list) {
      console.log('📄 Available Test Reports:\n');
      
      try {
        if (existsSync(reportsDir)) {
          const files = await fs.readdir(reportsDir);
          const reportFiles = files.filter(f => f.endsWith('.html') || f.endsWith('.json'));
          
          if (reportFiles.length === 0) {
            console.log('No reports found in the reports directory. Run tests to generate reports.');
          } else {
            reportFiles.forEach((file, index) => {
              console.log(`${index + 1}. ${file}`);
              const filePath = join(reportsDir, file);
              if (existsSync(filePath)) {
                const stats = require('fs').statSync(filePath);
                console.log(`   Created: ${stats.ctime.toLocaleString()}`);
                console.log(`   Size: ${this.formatFileSize(stats.size)}`);
              }
              console.log('');
            });
          }
        } else {
          console.log('Reports directory does not exist. Run tests to generate reports.');
        }
      } catch (error) {
                console.error(chalk.red(`❌ Failed to list reports: ${toMessage(error)}`));
      }
    }

    if (options.clean) {
      console.log('🧹 Cleaning old reports...');
      
      const retentionDays = parseInt(options.days);
      const cutoffDate = new Date(Date.now() - retentionDays * 24 * 60 * 60 * 1000);
      
      try {
        if (existsSync(reportsDir)) {
          const files = await fs.readdir(reportsDir);
          let cleaned = 0;
          
          for (const file of files) {
            const filePath = join(reportsDir, file);
            const stats = require('fs').statSync(filePath);
            
            if (stats.ctime < cutoffDate) {
              await fs.unlink(filePath);
              cleaned++;
            }
          }
          
          console.log(`✅ Cleaned ${cleaned} old reports (older than ${retentionDays} days)`);
        }
      } catch (error) {
                console.error(chalk.red(`❌ Failed to clean reports: ${toMessage(error)}`));
      }
    }
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
