/**
 * Conformance CLI Tests
 * Phase 2.2: Test suite for conformance CLI interface
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { ConformanceCli } from '../../src/cli/conformance-cli.js';
import { writeFileSync, unlinkSync, existsSync, readFileSync } from 'fs';

describe('ConformanceCli', () => {
  let cli: ConformanceCli;
  let consoleLogSpy: any;
  let consoleErrorSpy: any;
  let testFiles: string[] = [];

  beforeEach(() => {
    cli = new ConformanceCli();
    consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    testFiles = [];
  });

  afterEach(() => {
    consoleLogSpy.mockRestore();
    consoleErrorSpy.mockRestore();
    
    // Cleanup test files
    testFiles.forEach(file => {
      if (existsSync(file)) {
        unlinkSync(file);
      }
    });
  });

  describe('command creation', () => {
    it('should create CLI command with all subcommands', () => {
      const command = cli.createCommand();
      
      expect(command).toBeDefined();
      expect(command.name()).toBe('conformance');
      expect(command.description()).toContain('Runtime conformance verification');
      
      // Check that subcommands exist
      const subcommands = command.commands.map(cmd => cmd.name());
      expect(subcommands).toContain('verify');
      expect(subcommands).toContain('rules');
      expect(subcommands).toContain('config');
      expect(subcommands).toContain('metrics');
      expect(subcommands).toContain('status');
      expect(subcommands).toContain('sample');
    });
  });

  describe('verify command', () => {
    it('should handle valid input data', async () => {
      // Create test input file
      const inputData = {
        user: { email: 'test@example.com', name: 'Test User' },
        value: 42
      };
      const inputFile = 'test-input.json';
      writeFileSync(inputFile, JSON.stringify(inputData, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'verify', '--input', inputFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting conformance verification')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Loaded input data from ${inputFile}`)
      );
    });

    it('should handle missing input file', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'verify'];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Input file is required')
      );
    });

    it('should handle non-existent input file', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'verify', '--input', 'nonexistent.json'];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Input file not found')
      );
    });

    it('should load custom context file', async () => {
      const inputData = { test: true };
      const contextData = {
        timestamp: new Date().toISOString(),
        executionId: 'test-123',
        environment: 'test'
      };

      const inputFile = 'test-input.json';
      const contextFile = 'test-context.json';
      
      writeFileSync(inputFile, JSON.stringify(inputData, null, 2));
      writeFileSync(contextFile, JSON.stringify(contextData, null, 2));
      testFiles.push(inputFile, contextFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'verify', 
        '--input', inputFile,
        '--context-file', contextFile
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Loaded context from ${contextFile}`)
      );
    });

    it('should load custom rules file', async () => {
      const inputData = { test: true };
      const rules = [
        {
          id: 'test-rule-1',
          name: 'Test Rule',
          description: 'A test rule',
          category: 'data_validation',
          severity: 'minor',
          enabled: true,
          condition: {
            expression: 'true',
            variables: ['data'],
            constraints: {}
          },
          actions: ['log_violation'],
          metadata: {
            createdAt: new Date().toISOString(),
            updatedAt: new Date().toISOString(),
            version: '1.0.0',
            tags: ['test']
          }
        }
      ];

      const inputFile = 'test-input.json';
      const rulesFile = 'test-rules.json';
      
      writeFileSync(inputFile, JSON.stringify(inputData, null, 2));
      writeFileSync(rulesFile, JSON.stringify(rules, null, 2));
      testFiles.push(inputFile, rulesFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'verify', 
        '--input', inputFile,
        '--rules', rulesFile
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Loading 1 custom rules')
      );
    });

    it('should handle rule IDs filtering', async () => {
      const inputData = { test: true };
      const inputFile = 'test-input-filter.json';
      writeFileSync(inputFile, JSON.stringify(inputData, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'verify',
        '--input', inputFile,
        '--rule-ids', 'rule1,rule2,rule3'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting conformance verification')
      );
    });

    it('should handle category skipping', async () => {
      const inputData = { test: true };
      const inputFile = 'test-input-skip.json';
      writeFileSync(inputFile, JSON.stringify(inputData, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'verify',
        '--input', inputFile,
        '--skip-categories', 'api_contract,security_policy'
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting conformance verification')
      );
    });

    it('should save results to output file', async () => {
      const inputData = { test: true };
      const inputFile = 'test-input-output.json';
      const outputFile = 'test-output.json';
      
      writeFileSync(inputFile, JSON.stringify(inputData, null, 2));
      testFiles.push(inputFile, outputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'verify',
        '--input', inputFile,
        '--output', outputFile
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Results saved to ${outputFile}`)
      );
      expect(existsSync(outputFile)).toBe(true);
    });
  });

  describe('rules command', () => {
    it('should list all rules', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'rules', '--list'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('conformance rules')
      );
    });

    it('should filter rules by category', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'rules', '--list', '--category', 'data_validation'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('conformance rules')
      );
    });

    it('should add rules from file', async () => {
      const newRules = [
        {
          id: 'new-rule-1',
          name: 'New Test Rule',
          description: 'A new test rule',
          category: 'data_validation',
          severity: 'major',
          enabled: true,
          condition: {
            expression: 'true',
            variables: ['data'],
            constraints: {}
          },
          actions: ['log_violation'],
          metadata: {
            createdAt: new Date().toISOString(),
            updatedAt: new Date().toISOString(),
            version: '1.0.0',
            tags: ['test']
          }
        }
      ];

      const rulesFile = 'new-rules.json';
      writeFileSync(rulesFile, JSON.stringify(newRules, null, 2));
      testFiles.push(rulesFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'rules', '--add', rulesFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Adding 1 rules')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Added rule: New Test Rule')
      );
    });

    it('should export rules to file', async () => {
      const exportFile = 'exported-rules.json';
      testFiles.push(exportFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'rules', '--export', exportFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Exported`)
      );
      expect(existsSync(exportFile)).toBe(true);
    });

    it('should import rules from file', async () => {
      const rules = [
        {
          id: 'import-rule-1',
          name: 'Imported Rule',
          description: 'An imported rule',
          category: 'api_contract',
          severity: 'minor',
          enabled: true,
          condition: {
            expression: 'true',
            variables: ['data'],
            constraints: {}
          },
          actions: ['log_violation'],
          metadata: {
            createdAt: new Date().toISOString(),
            updatedAt: new Date().toISOString(),
            version: '1.0.0',
            tags: ['imported']
          }
        }
      ];

      const importFile = 'import-rules.json';
      writeFileSync(importFile, JSON.stringify(rules, null, 2));
      testFiles.push(importFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'rules', '--import', importFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Importing 1 rules')
      );
    });
  });

  describe('config command', () => {
    it('should show current configuration', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'config', '--show'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Current Configuration')
      );
    });

    it('should update configuration from file', async () => {
      const newConfig = {
        enabled: false,
        mode: 'strict'
      };

      const configFile = 'new-config.json';
      writeFileSync(configFile, JSON.stringify(newConfig, null, 2));
      testFiles.push(configFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'config', '--update', configFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Configuration updated')
      );
    });

    it('should set individual configuration values', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'config', '--set', 'enabled=false'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Set enabled = false')
      );
    });

    it('should export configuration', async () => {
      const exportFile = 'exported-config.json';
      testFiles.push(exportFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'config', '--export', exportFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Configuration exported')
      );
      expect(existsSync(exportFile)).toBe(true);
    });

    it('should reset configuration', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'config', '--reset'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Configuration reset to defaults')
      );
    });
  });

  describe('metrics command', () => {
    it('should display metrics in table format', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'metrics', '--format', 'table'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Conformance Metrics')
      );
    });

    it('should display metrics in JSON format', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'metrics', '--format', 'json'];

      await command.parseAsync(args);

      // Should output JSON (look for JSON structure indicators)
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringMatching(/[{}\[\]":]/)
      );
    });

    it('should export metrics to file', async () => {
      const metricsFile = 'metrics-export.json';
      testFiles.push(metricsFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'metrics', '--export', metricsFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Metrics exported')
      );
    });

    it('should reset metrics', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'metrics', '--reset'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Metrics reset')
      );
    });
  });

  describe('status command', () => {
    it('should show system status', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'status'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Conformance Verification Engine Status')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Version: 2.2.0')
      );
    });

    it('should show monitor information', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'status', '--monitors'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Active Monitors')
      );
    });

    it('should show handler information', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'status', '--handlers'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Violation Handlers')
      );
    });
  });

  describe('sample command', () => {
    it('should generate sample rules', async () => {
      const rulesFile = 'sample-rules-test.json';
      testFiles.push(rulesFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'sample', '--rules', rulesFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Sample rules generated')
      );
      expect(existsSync(rulesFile)).toBe(true);

      // Verify content is valid JSON
      const content = readFileSync(rulesFile, 'utf-8');
      const rules = JSON.parse(content);
      expect(Array.isArray(rules)).toBe(true);
      expect(rules.length).toBeGreaterThan(0);
    });

    it('should generate sample config', async () => {
      const configFile = 'sample-config-test.json';
      testFiles.push(configFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'sample', '--config', configFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Sample config generated')
      );
      expect(existsSync(configFile)).toBe(true);
    });

    it('should generate sample data', async () => {
      const dataFile = 'sample-data-test.json';
      testFiles.push(dataFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'sample', '--data', dataFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Sample data generated')
      );
      expect(existsSync(dataFile)).toBe(true);
    });

    it('should generate sample context', async () => {
      const contextFile = 'sample-context-test.json';
      testFiles.push(contextFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'sample', '--context', contextFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Sample context generated')
      );
      expect(existsSync(contextFile)).toBe(true);
    });

    it('should generate all sample files', async () => {
      const rulesFile = 'all-sample-rules.json';
      const configFile = 'all-sample-config.json';
      const dataFile = 'all-sample-data.json';
      const contextFile = 'all-sample-context.json';
      
      testFiles.push(rulesFile, configFile, dataFile, contextFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'sample',
        '--rules', rulesFile,
        '--config', configFile,
        '--data', dataFile,
        '--context', contextFile
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Sample files generation complete')
      );
      
      expect(existsSync(rulesFile)).toBe(true);
      expect(existsSync(configFile)).toBe(true);
      expect(existsSync(dataFile)).toBe(true);
      expect(existsSync(contextFile)).toBe(true);
    });
  });

  describe('error handling', () => {
    it('should handle invalid JSON in input file', async () => {
      const invalidFile = 'invalid.json';
      writeFileSync(invalidFile, '{ invalid json }');
      testFiles.push(invalidFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'verify', '--input', invalidFile];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Verification failed')
      );
    });

    it('should handle invalid configuration values', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'config', '--set', 'invalid_format'];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Invalid format')
      );
    });

    it('should handle missing files gracefully', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'rules', '--add', 'nonexistent.json'];

      await command.parseAsync(args);

      // Should not crash, just not perform the operation
      expect(consoleLogSpy).not.toHaveBeenCalledWith(
        expect.stringContaining('Adding')
      );
    });
  });

  describe('integration workflow', () => {
    it('should support complete workflow', async () => {
      // 1. Generate sample files
      const rulesFile = 'workflow-rules.json';
      const dataFile = 'workflow-data.json';
      const configFile = 'workflow-config.json';
      const resultsFile = 'workflow-results.json';
      
      testFiles.push(rulesFile, dataFile, configFile, resultsFile);

      let command = cli.createCommand();
      
      // Generate samples
      await command.parseAsync([
        'node', 'cli', 'sample',
        '--rules', rulesFile,
        '--data', dataFile,
        '--config', configFile
      ]);

      // Update config
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'config', '--update', configFile
      ]);

      // Add rules
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'rules', '--add', rulesFile
      ]);

      // Run verification
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'verify',
        '--input', dataFile,
        '--output', resultsFile
      ]);

      // Check metrics
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'metrics'
      ]);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Sample files generation complete')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Configuration updated')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Added rule')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting conformance verification')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Conformance Metrics')
      );
    });
  });
});