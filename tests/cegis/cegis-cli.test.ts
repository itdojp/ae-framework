/**
 * CEGIS CLI Tests
 * Phase 2.1: Test suite for CEGIS command-line interface
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { CEGISCli } from '../../src/cli/cegis-cli.js';
import { writeFileSync, unlinkSync, existsSync } from 'fs';
import { FailureArtifactFactory } from '../../src/cegis/failure-artifact-factory.js';

describe('CEGISCli', () => {
  let cli: CEGISCli;
  let consoleLogSpy: any;
  let consoleErrorSpy: any;
  let testFiles: string[] = [];

  beforeEach(() => {
    cli = new CEGISCli();
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
      expect(command.name()).toBe('fix');
      expect(command.description()).toContain('CEGIS-based automated code fixing');
      
      // Check that subcommands exist
      const subcommands = command.commands.map(cmd => cmd.name());
      expect(subcommands).toContain('apply');
      expect(subcommands).toContain('analyze');
      expect(subcommands).toContain('create-artifact');
      expect(subcommands).toContain('status');
      expect(subcommands).toContain('strategies');
    });
  });

  describe('apply command', () => {
    it('should handle valid failure artifacts file', async () => {
      // Create test failure artifacts
      const failures = [
        FailureArtifactFactory.fromTypeError(
          "Cannot find name 'testVar'",
          '/test.ts',
          10,
          5
        ),
        FailureArtifactFactory.fromTestFailure(
          'test should pass',
          'expected',
          'actual'
        )
      ];

      const inputFile = 'test-failures.json';
      writeFileSync(inputFile, JSON.stringify(failures, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'apply', '--input', inputFile, '--dry-run'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting CEGIS auto-fix process')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Loaded 2 failure artifacts')
      );
    });

    it('should handle missing input file gracefully', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'apply', '--input', 'nonexistent.json', '--dry-run'];

      await expect(command.parseAsync(args)).rejects.toThrow();
      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Input file not found')
      );
    });

    it('should validate confidence threshold', async () => {
      const failures = [
        FailureArtifactFactory.fromError(new Error('test error'))
      ];

      const inputFile = 'test-invalid-confidence.json';
      writeFileSync(inputFile, JSON.stringify(failures, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'apply', 
        '--input', inputFile,
        '--confidence', '2.0', // Invalid confidence > 1.0
        '--dry-run'
      ];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Confidence threshold must be between 0.0 and 1.0')
      );
    });

    it('should validate risk level', async () => {
      const failures = [
        FailureArtifactFactory.fromError(new Error('test error'))
      ];

      const inputFile = 'test-invalid-risk.json';
      writeFileSync(inputFile, JSON.stringify(failures, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'apply',
        '--input', inputFile,
        '--max-risk', '10', // Invalid risk > 5
        '--dry-run'
      ];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Risk level must be between 1 and 5')
      );
    });

    it('should handle no input file provided', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'apply', '--dry-run'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('No input file specified')
      );
    });
  });

  describe('analyze command', () => {
    it('should analyze failure patterns', async () => {
      // Create test failures with patterns
      const failures = [
        FailureArtifactFactory.fromTypeError("Cannot find name 'var1'", '/file1.ts', 10, 5),
        FailureArtifactFactory.fromTypeError("Cannot find name 'var2'", '/file2.ts', 15, 10),
        FailureArtifactFactory.fromTestFailure('test1', 'expected1', 'actual1'),
        FailureArtifactFactory.fromTestFailure('test2', 'expected2', 'actual2')
      ];

      const inputFile = 'test-analysis.json';
      writeFileSync(inputFile, JSON.stringify(failures, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'analyze', '--input', inputFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Analyzing failure patterns')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Total Failures: 4')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('type_error')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('test_failure')
      );
    });

    it('should show verbose analysis when requested', async () => {
      const failures = [
        FailureArtifactFactory.fromContractViolation(
          'TestSchema',
          'input',
          { invalid: 'data' },
          { filePath: '/api/test.ts', startLine: 5, endLine: 5 }
        )
      ];

      const inputFile = 'test-verbose.json';
      writeFileSync(inputFile, JSON.stringify(failures, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'analyze', '--input', inputFile, '--verbose'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Detailed Analysis')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Contract Violation: TestSchema')
      );
    });

    it('should handle empty failure list', async () => {
      const inputFile = 'test-empty.json';
      writeFileSync(inputFile, JSON.stringify([], null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'analyze', '--input', inputFile];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('No failure artifacts found')
      );
    });
  });

  describe('create-artifact command', () => {
    it('should create error artifact', async () => {
      const outputFile = 'test-error-artifact.json';
      testFiles.push(outputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'create-artifact',
        '--type', 'error',
        '--message', 'Test runtime error',
        '--file', '/test/error.ts',
        '--line', '25',
        '--output', outputFile
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Creating failure artifact')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Failure artifact created: ${outputFile}`)
      );
      
      expect(existsSync(outputFile)).toBe(true);
    });

    it('should create test failure artifact', async () => {
      const outputFile = 'test-failure-artifact.json';
      testFiles.push(outputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'create-artifact',
        '--type', 'test',
        '--message', 'Test assertion failed',
        '--file', '/test/spec.ts',
        '--output', outputFile
      ];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining(`Failure artifact created: ${outputFile}`)
      );
      
      expect(existsSync(outputFile)).toBe(true);
    });

    it('should create type error artifact', async () => {
      const outputFile = 'test-type-artifact.json';
      testFiles.push(outputFile);

      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'create-artifact',
        '--type', 'type',
        '--message', 'TypeScript compilation error',
        '--file', '/src/types.ts',
        '--line', '15',
        '--column', '8',
        '--output', outputFile
      ];

      await command.parseAsync(args);

      expect(existsSync(outputFile)).toBe(true);
    });

    it('should handle missing message', async () => {
      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'create-artifact',
        '--type', 'error',
        '--output', 'test-missing-message.json'
      ];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Error message is required')
      );
    });

    it('should handle unknown artifact type', async () => {
      const command = cli.createCommand();
      const args = [
        'node', 'cli', 'create-artifact',
        '--type', 'unknown',
        '--message', 'Test message',
        '--output', 'test-unknown.json'
      ];

      await command.parseAsync(args);

      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Unknown artifact type: unknown')
      );
    });
  });

  describe('status command', () => {
    it('should display system status', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'status'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('CEGIS System Status')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Version: 1.0.0')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Available Strategies')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('type_error')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Configuration')
      );
    });
  });

  describe('strategies command', () => {
    it('should list all strategies', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'strategies'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Available Fix Strategies')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('TYPE_ERROR')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('TEST_FAILURE')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('CONTRACT_VIOLATION')
      );
    });

    it('should filter strategies by category', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'strategies', '--category', 'type_error'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('TYPE_ERROR')
      );
      // Should not show other categories
      expect(consoleLogSpy).not.toHaveBeenCalledWith(
        expect.stringContaining('TEST_FAILURE')
      );
    });

    it('should handle unknown category', async () => {
      const command = cli.createCommand();
      const args = ['node', 'cli', 'strategies', '--category', 'unknown_category'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('unknown_category: No strategies available')
      );
    });
  });

  describe('error handling', () => {
    it('should handle malformed JSON input', async () => {
      const inputFile = 'test-malformed.json';
      writeFileSync(inputFile, '{ invalid json }');
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'apply', '--input', inputFile, '--dry-run'];

      await expect(command.parseAsync(args)).rejects.toThrow();
      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Failed to parse input file')
      );
    });

    it('should handle invalid artifact in input', async () => {
      const inputFile = 'test-invalid-artifact.json';
      writeFileSync(inputFile, JSON.stringify([
        { id: 'invalid', title: 'Missing required fields' }
      ]));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'apply', '--input', inputFile, '--dry-run'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Invalid artifact skipped')
      );
    });

    it('should handle single artifact format', async () => {
      const artifact = FailureArtifactFactory.fromError(new Error('single error'));
      
      const inputFile = 'test-single.json';
      writeFileSync(inputFile, JSON.stringify(artifact, null, 2));
      testFiles.push(inputFile);

      const command = cli.createCommand();
      const args = ['node', 'cli', 'apply', '--input', inputFile, '--dry-run'];

      await command.parseAsync(args);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Loaded 1 failure artifacts')
      );
    });
  });

  describe('integration', () => {
    it('should work with complete workflow', async () => {
      // Create artifact
      const createOutputFile = 'workflow-artifact.json';
      testFiles.push(createOutputFile);

      let command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'create-artifact',
        '--type', 'error',
        '--message', 'Integration test error',
        '--file', '/integration/test.ts',
        '--output', createOutputFile
      ]);

      // Analyze artifacts
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'analyze',
        '--input', createOutputFile
      ]);

      // Apply fixes
      command = cli.createCommand();
      await command.parseAsync([
        'node', 'cli', 'apply',
        '--input', createOutputFile,
        '--dry-run',
        '--confidence', '0.5'
      ]);

      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Failure artifact created')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Analyzing failure patterns')
      );
      expect(consoleLogSpy).toHaveBeenCalledWith(
        expect.stringContaining('Starting CEGIS auto-fix process')
      );
    });
  });
});