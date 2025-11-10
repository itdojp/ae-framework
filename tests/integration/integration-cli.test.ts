/**
 * Integration Testing CLI Tests
 * Phase 2.3: Test suite for integration testing CLI interface
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { IntegrationTestingCli } from '../../src/cli/integration-cli.js';
import { writeFileSync, existsSync, mkdirSync } from 'fs';
import { join } from 'path';
import { createIntegrationTempDir, applyIntegrationRetry } from '../_helpers/integration-test-utils.js';

applyIntegrationRetry(it);

describe('IntegrationTestingCli', () => {
  let cli: IntegrationTestingCli;
  let consoleLogSpy: any;
  let consoleErrorSpy: any;
  let tempDir: string;
  let cwdSpy: ReturnType<typeof vi.spyOn>;
  const inTemp = (name: string): string => join(tempDir, name);

  beforeEach(async () => {
    tempDir = await createIntegrationTempDir('integration-cli-');
    cwdSpy = vi.spyOn(process, 'cwd').mockReturnValue(tempDir);
    cli = new IntegrationTestingCli();
    consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    cwdSpy.mockRestore();
    consoleLogSpy.mockRestore();
    consoleErrorSpy.mockRestore();
  });

  describe('command creation', () => {
    it('should create CLI command with all subcommands', () => {
      const command = cli.createCommand();
      
      expect(command).toBeDefined();
      expect(command.name()).toBe('integration');
      expect(command.description()).toContain('integration testing');
      
      const subcommands = command.commands.map(cmd => cmd.name());
      expect(subcommands).toContain('run');
      expect(subcommands).toContain('discover');
      expect(subcommands).toContain('list');
      expect(subcommands).toContain('generate');
      expect(subcommands).toContain('status');
      expect(subcommands).toContain('reports');
    });
  });

  describe('discover command', () => {
    it('should discover tests from JSON files', async () => {
      // Create sample test file
      const testData = [{
        id: 'test-1',
        name: 'Sample Test',
        description: 'A sample test case',
        category: 'e2e',
        severity: 'major',
        enabled: true,
        preconditions: [],
        steps: [],
        expectedResults: [],
        fixtures: [],
        dependencies: [],
        tags: [],
        metadata: {
          complexity: 'low',
          stability: 'stable',
          lastUpdated: new Date().toISOString()
        }
      }];

      const testFile = inTemp('test-discovery.json');
      writeFileSync(testFile, JSON.stringify(testData, null, 2));

      const command = cli.createCommand();
      const args = ['node', 'cli', 'discover', '--patterns', testFile, '--type', 'tests'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Discovering test resources')
      );
    });

    it('should discover all resource types', async () => {
      // Create sample files for each type
      const testData = createSampleTestData();
      const suiteData = createSampleSuiteData();
      const fixtureData = createSampleFixtureData();

      const testFile = inTemp('discover-tests.json');
      const suiteFile = inTemp('discover-suites.json');
      const fixtureFile = inTemp('discover-fixtures.json');

      writeFileSync(testFile, JSON.stringify([testData], null, 2));
      writeFileSync(suiteFile, JSON.stringify([suiteData], null, 2));
      writeFileSync(fixtureFile, JSON.stringify([fixtureData], null, 2));

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'discover', 
        '--patterns', `${testFile},${suiteFile},${fixtureFile}`,
        '--type', 'all'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Discovery Summary')
      );
    });

    it('should save discovery results to file', async () => {
      const testData = createSampleTestData();
      const testFile = inTemp('discover-input.json');
      const outputFile = inTemp('discovery-output.json');

      writeFileSync(testFile, JSON.stringify([testData], null, 2));

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'discover',
        '--patterns', testFile,
        '--type', 'tests',
        '--output', outputFile
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Results saved to ${outputFile}`)
      );
      expect(existsSync(outputFile)).toBe(true);
    });

    it('should handle invalid patterns gracefully', async () => {
      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'discover',
        '--patterns', 'nonexistent-file.json',
        '--type', 'tests'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Discovering test resources')
      );
    });
  });

  describe('list command', () => {
    it('should list environments', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'list', '--type', 'environments'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Available environments')
      );
    });

    it('should list runners', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'list', '--type', 'runners'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Available runners')
      );
    });

    it('should list reporters', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'list', '--type', 'reporters'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Available reporters')
      );
    });

    it('should handle unknown resource type', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'list', '--type', 'unknown'];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Unknown resource type: unknown')
      );
    });
  });

  describe('generate command', () => {
    it('should generate sample test', async () => {
      const outputFile = 'generated-test.json';

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'generate',
        '--type', 'test',
        '--output', outputFile,
        '--test-type', 'e2e',
        '--name', 'Generated E2E Test'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Generating sample test')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Generated test saved to ${outputFile}`)
      );
      expect(existsSync(outputFile)).toBe(true);
    });

    it('should generate sample suite', async () => {
      const outputFile = 'generated-suite.json';

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'generate',
        '--type', 'suite',
        '--output', outputFile,
        '--name', 'Generated Test Suite'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Generated suite saved to')
      );
      expect(existsSync(outputFile)).toBe(true);
    });

    it('should generate sample fixture', async () => {
      const outputFile = 'generated-fixture.json';

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'generate',
        '--type', 'fixture',
        '--output', outputFile,
        '--name', 'Generated Fixture'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Generated fixture saved to')
      );
      expect(existsSync(outputFile)).toBe(true);
    });

    it('should generate sample environment', async () => {
      const outputFile = 'generated-environment.json';

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'generate',
        '--type', 'environment',
        '--output', outputFile,
        '--name', 'test-env'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Generated environment saved to')
      );
      expect(existsSync(outputFile)).toBe(true);
    });

    it('should output to console without file', async () => {
      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'generate',
        '--type', 'test',
        '--test-type', 'api'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('"id"')
      );
    });

    it('should handle unknown generation type', async () => {
      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'generate',
        '--type', 'unknown'
      ];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Generation failed')
      );
    });
  });

  describe('status command', () => {
    it('should show system status', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'status'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Integration Testing System Status')
      );
    });

    it('should handle watch mode setup', async () => {
      // Mock setInterval to prevent actual watching
      const originalSetInterval = global.setInterval;
      const mockSetInterval = vi.fn();
      global.setInterval = mockSetInterval;

      const command = cli.createCommand();
      const args = ['node', 'cli', 'status', '--watch', '--refresh', '2'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Watching test execution status')
      );

      // Restore original
      global.setInterval = originalSetInterval;
    });
  });

  describe('reports command', () => {
    it('should list reports when directory exists', async () => {
      // Create test reports directory
      const reportsDir = inTemp('test-results');
      if (!existsSync(reportsDir)) {
        mkdirSync(reportsDir, { recursive: true });
      }

      // Create sample report files
      const reportFiles = ['report1.html', 'report2.json'];
      reportFiles.forEach(file => {
        const filePath = join(reportsDir, file);
        writeFileSync(filePath, 'sample report content');
      });

      const command = cli.createCommand();
      const args = ['node', 'cli', 'reports', '--list'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Available Test Reports')
      );
    });

    it('should handle no reports directory', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'reports', '--list'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('No reports found in the reports directory')
      );
    });

    it('should clean old reports', async () => {
      const reportsDir = inTemp('test-results');
      if (!existsSync(reportsDir)) {
        mkdirSync(reportsDir, { recursive: true });
      }

      // Create old report file
      const oldReportPath = join(reportsDir, 'old-report.html');
      writeFileSync(oldReportPath, 'old report');
      
      // Modify file time to make it appear old (simplified)

      const command = cli.createCommand();
      const args = ['node', 'cli', 'reports', '--clean', '--days', '0'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Cleaning old reports')
      );
    });
  });

  describe('run command', () => {
    it('should handle no tests found', async () => {
      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'run',
        '--suites', 'nonexistent.json',
        '--environment', 'default'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('No tests or suites found')
      );
    });

    it('should run with test suites', async () => {
      // Create sample test and suite
      const testData = createSampleTestData();
      const suiteData = {
        ...createSampleSuiteData(),
        tests: [testData.id]
      };

      const testFile = 'run-test.json';
      const suiteFile = 'run-suite.json';

      writeFileSync(testFile, JSON.stringify([testData], null, 2));
      writeFileSync(suiteFile, JSON.stringify([suiteData], null, 2));

      const outputDir = './test-results-run';

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'run',
        '--suites', suiteFile,
        '--tests', testFile,
        '--environment', 'default',
        '--output-dir', outputDir,
        '--timeout', '30000'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting integration test execution')
      );
    });

    it('should handle execution filters', async () => {
      const testData = createSampleTestData();
      const testFile = 'filtered-test.json';
      writeFileSync(testFile, JSON.stringify([testData], null, 2));

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'run',
        '--tests', testFile,
        '--categories', 'e2e,integration',
        '--tags', 'smoke',
        '--exclude', 'excluded-test',
        '--environment', 'default'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting integration test execution')
      );
    });

    it('should handle parallel execution options', async () => {
      const testData = createSampleTestData();
      const testFile = 'parallel-test.json';
      writeFileSync(testFile, JSON.stringify([testData], null, 2));

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'run',
        '--tests', testFile,
        '--parallel',
        '--max-concurrency', '2',
        '--fail-fast',
        '--environment', 'default'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting integration test execution')
      );
    });
  });

  describe('error handling', () => {
    it('should handle CLI execution errors gracefully', async () => {
      const command = cli.createCommand();
      
      // Force an error by passing invalid arguments
      const args = ['node', 'cli', 'invalid-command'];

      try {
        await command.parseAsync(args);
      } catch (error) {
        // Expected to throw for invalid command
      }

      // CLI should handle errors internally for most commands
    });

    it('should validate command options', async () => {
      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'generate',
        '--type', 'invalid-type'
      ];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Generation failed')
      );
    });
  });

  describe('integration workflow', () => {
    it('should support complete testing workflow', async () => {
      // 1. Generate sample test
      const testFile = 'workflow-test.json';

      let command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'generate',
        '--type', 'test',
        '--output', testFile,
        '--test-type', 'e2e'
      ]);

      // 2. Discover the generated test
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'discover',
        '--patterns', testFile,
        '--type', 'tests'
      ]);

      // 3. List available resources
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'list',
        '--type', 'environments'
      ]);

      // 4. Check system status
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'status'
      ]);

      // 5. Run the test (will fail due to mock implementation, but should not crash)
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'run',
        '--tests', testFile,
        '--environment', 'default'
      ]);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Generated test saved to')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Discovering test resources')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Available environments')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Integration Testing System Status')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting integration test execution')
      );
    });
  });

  // Helper functions
  function createSampleTestData() {
    return {
      id: 'sample-test-' + Date.now(),
      name: 'Sample Test',
      description: 'A sample test case for testing',
      category: 'e2e',
      severity: 'major',
      enabled: true,
      preconditions: [],
      steps: [{
        id: 'step-1',
        description: 'Sample step',
        action: 'navigate:/',
        data: {},
        expectedResult: 'Success'
      }],
      expectedResults: ['Test passes'],
      fixtures: [],
      dependencies: [],
      tags: ['sample', 'smoke'],
      metadata: {
        complexity: 'low',
        stability: 'stable',
        lastUpdated: new Date().toISOString()
      }
    };
  }

  function createSampleSuiteData() {
    return {
      id: 'sample-suite-' + Date.now(),
      name: 'Sample Suite',
      description: 'A sample test suite for testing',
      category: 'e2e',
      tests: [],
      fixtures: [],
      configuration: {
        parallel: false,
        maxConcurrency: 1,
        timeout: 60000,
        retries: 1,
        skipOnFailure: false,
        failFast: false
      },
      setup: [],
      teardown: [],
      metadata: {
        priority: 'medium',
        tags: ['sample', 'suite']
      }
    };
  }

  function createSampleFixtureData() {
    return {
      id: 'sample-fixture-' + Date.now(),
      name: 'Sample Fixture',
      description: 'A sample test fixture for testing',
      category: 'unit',
      data: { sampleData: true },
      setup: [],
      teardown: [],
      dependencies: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['sample', 'fixture']
      }
    };
  }
});
