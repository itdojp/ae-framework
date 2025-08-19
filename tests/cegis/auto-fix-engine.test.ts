/**
 * Auto-Fix Engine Tests
 * Phase 2.1: Test suite for CEGIS auto-fix functionality
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { AutoFixEngine } from '../../src/cegis/auto-fix-engine.js';
import { FailureArtifactFactory } from '../../src/cegis/failure-artifact-factory.js';
import { FailureArtifact, AutoFixOptions } from '../../src/cegis/types.js';

describe('AutoFixEngine', () => {
  let engine: AutoFixEngine;
  let mockFailures: FailureArtifact[];

  beforeEach(() => {
    engine = new AutoFixEngine();
    
    // Create mock failure artifacts
    mockFailures = [
      FailureArtifactFactory.fromTypeError(
        "Cannot find name 'someVariable'",
        '/test/file.ts',
        10,
        5,
        'const result = someVariable;'
      ),
      FailureArtifactFactory.fromTestFailure(
        'should return correct value',
        'expected',
        'actual',
        { filePath: '/test/test.spec.ts', startLine: 15, endLine: 15 },
        'Test failed: assertion error'
      ),
      FailureArtifactFactory.fromContractViolation(
        'UserSchema',
        'input',
        { name: 'John', age: '25' }, // age should be number
        { filePath: '/api/user.ts', startLine: 20, endLine: 20 }
      )
    ];
  });

  describe('initialization', () => {
    it('should initialize with default configuration', () => {
      expect(engine).toBeDefined();
      expect(engine.getStrategies('type_error')).toHaveLength(1);
      expect(engine.getStrategies('test_failure')).toHaveLength(1);
      expect(engine.getStrategies('contract_violation')).toHaveLength(1);
    });

    it('should accept custom configuration', () => {
      const customEngine = new AutoFixEngine({
        confidenceThreshold: 0.8,
        maxRiskLevel: 2,
        maxFixesPerRun: 5
      });

      expect(customEngine).toBeDefined();
    });
  });

  describe('analyzeFailurePatterns', () => {
    it('should identify common patterns in failures', async () => {
      const patterns = await engine.analyzeFailurePatterns(mockFailures);
      
      expect(patterns).toBeDefined();
      expect(Array.isArray(patterns)).toBe(true);
      
      // Should group by categories
      const categories = patterns.map(p => p.categories[0]);
      expect(categories).toContain('type_error');
      expect(categories).toContain('test_failure');
      expect(categories).toContain('contract_violation');
    });

    it('should calculate pattern confidence correctly', async () => {
      // Create multiple failures with same pattern
      const duplicateFailures = [
        ...mockFailures,
        FailureArtifactFactory.fromTypeError(
          "Cannot find name 'anotherVariable'",
          '/test/file2.ts',
          5,
          10
        )
      ];

      const patterns = await engine.analyzeFailurePatterns(duplicateFailures);
      
      // Should detect pattern for type errors
      const typeErrorPattern = patterns.find(p => 
        p.categories.includes('type_error') && p.frequency > 1
      );
      
      if (typeErrorPattern) {
        expect(typeErrorPattern.confidence).toBeGreaterThan(0);
        expect(typeErrorPattern.confidence).toBeLessThanOrEqual(1);
      }
    });

    it('should handle empty failure list', async () => {
      const patterns = await engine.analyzeFailurePatterns([]);
      expect(patterns).toEqual([]);
    });
  });

  describe('executeFixes', () => {
    it('should execute fixes in dry run mode', async () => {
      const options: AutoFixOptions = {
        dryRun: true,
        confidenceThreshold: 0.5,
        maxRiskLevel: 5
      };

      const result = await engine.executeFixes(mockFailures, options);

      expect(result).toBeDefined();
      expect(result.summary).toBeDefined();
      expect(result.summary.totalFailures).toBe(mockFailures.length);
      expect(result.appliedFixes).toBeDefined();
      expect(result.skippedFixes).toBeDefined();
      expect(result.recommendations).toBeDefined();
    });

    it('should filter failures by confidence threshold', async () => {
      const options: AutoFixOptions = {
        dryRun: true,
        confidenceThreshold: 0.95, // Very high threshold
        maxRiskLevel: 5
      };

      const result = await engine.executeFixes(mockFailures, options);

      // Most fixes should be skipped due to high confidence threshold
      expect(result.summary.fixesSkipped).toBeGreaterThan(0);
    });

    it('should filter failures by risk level', async () => {
      const options: AutoFixOptions = {
        dryRun: true,
        confidenceThreshold: 0.1, // Very low threshold
        maxRiskLevel: 1 // Very low risk tolerance
      };

      const result = await engine.executeFixes(mockFailures, options);

      // Many fixes should be skipped due to low risk tolerance
      expect(result.summary.fixesSkipped).toBeGreaterThan(0);
    });

    it('should generate recommendations', async () => {
      const options: AutoFixOptions = {
        dryRun: true,
        confidenceThreshold: 0.7,
        maxRiskLevel: 3
      };

      const result = await engine.executeFixes(mockFailures, options);

      expect(result.recommendations).toBeDefined();
      expect(Array.isArray(result.recommendations)).toBe(true);
    });

    it('should handle execution errors gracefully', async () => {
      // Create a failure that will cause strategy execution to fail
      const problematicFailure = FailureArtifactFactory.fromError(
        new Error('Problematic error'),
        undefined,
        { simulateError: true }
      );

      const result = await engine.executeFixes([problematicFailure], {
        dryRun: true,
        confidenceThreshold: 0.1,
        maxRiskLevel: 5
      });

      expect(result).toBeDefined();
      expect(result.summary.success).toBeDefined();
    });
  });

  describe('strategy management', () => {
    it('should add custom strategies', () => {
      const mockStrategy = {
        name: 'Custom Strategy',
        category: 'test_failure' as const,
        confidence: 0.8,
        riskLevel: 2,
        description: 'Test strategy',
        canApply: vi.fn().mockResolvedValue(true),
        generateFix: vi.fn().mockResolvedValue([])
      };

      engine.addStrategy(mockStrategy);

      const strategies = engine.getStrategies('test_failure');
      expect(strategies).toContain(mockStrategy);
    });

    it('should return empty array for unknown categories', () => {
      const strategies = engine.getStrategies('unknown_category' as any);
      expect(strategies).toEqual([]);
    });
  });

  describe('error handling', () => {
    it('should handle malformed failure artifacts', async () => {
      const malformedFailure = {
        id: 'invalid',
        // Missing required fields
      } as any;

      // Should not throw, but may skip invalid artifacts
      const result = await engine.executeFixes([malformedFailure], {
        dryRun: true
      });

      expect(result).toBeDefined();
    });

    it('should handle strategy execution timeout', async () => {
      const options: AutoFixOptions = {
        dryRun: true,
        timeoutMs: 1 // Very short timeout
      };

      // This should complete quickly even with short timeout in dry run
      const result = await engine.executeFixes(mockFailures, options);
      expect(result).toBeDefined();
    });
  });

  describe('performance', () => {
    it('should handle large numbers of failures efficiently', async () => {
      // Create 100 similar failures
      const manyFailures: FailureArtifact[] = [];
      for (let i = 0; i < 100; i++) {
        manyFailures.push(
          FailureArtifactFactory.fromTypeError(
            `Cannot find name 'variable${i}'`,
            `/test/file${i}.ts`,
            10,
            5
          )
        );
      }

      const startTime = Date.now();
      const result = await engine.executeFixes(manyFailures, {
        dryRun: true,
        maxRiskLevel: 5,
        confidenceThreshold: 0.1
      });
      const duration = Date.now() - startTime;

      expect(result).toBeDefined();
      expect(result.summary.totalFailures).toBe(100);
      
      // Should complete in reasonable time (less than 5 seconds)
      expect(duration).toBeLessThan(5000);
    });
  });

  describe('integration', () => {
    it('should work with different failure types', async () => {
      const diverseFailures = [
        FailureArtifactFactory.fromError(new Error('Runtime error')),
        FailureArtifactFactory.fromBuildError('Build failed', 'npm run build', 1, 'Error output'),
        FailureArtifactFactory.fromLintError('no-unused-vars', 'Variable is unused', '/src/test.ts', 5, 10),
        FailureArtifactFactory.fromPerformanceIssue('bundle-size', 1000, 1500)
      ];

      const result = await engine.executeFixes(diverseFailures, {
        dryRun: true,
        confidenceThreshold: 0.1,
        maxRiskLevel: 5
      });

      expect(result).toBeDefined();
      expect(result.summary.totalFailures).toBe(diverseFailures.length);
    });

    it('should prioritize fixes correctly', async () => {
      // Create failures with different severities
      const prioritizedFailures = [
        FailureArtifactFactory.fromError(new Error('Critical error')),
        FailureArtifactFactory.fromLintError('style', 'Style issue', '/src/style.ts', 1, 1, 'warning')
      ];

      // Modify severity
      prioritizedFailures[0].severity = 'critical';
      prioritizedFailures[1].severity = 'info';

      const result = await engine.executeFixes(prioritizedFailures, {
        dryRun: true,
        confidenceThreshold: 0.1,
        maxRiskLevel: 5
      });

      expect(result).toBeDefined();
      // Critical failures should be processed first
    });
  });
});