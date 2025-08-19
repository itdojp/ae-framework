/**
 * Tests for CEGIS Auto-Fix Engine
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  AutoFixEngine,
  AutoFixOptions,
  FixStrategy,
} from '../../src/cegis/auto-fix-engine.js';
import {
  FailureArtifact,
  FailureArtifactFactory,
  FailureCategory,
  FailureSeverity,
} from '../../src/cegis/failure-artifact-schema.js';

describe('AutoFixEngine', () => {
  let engine: AutoFixEngine;
  let defaultOptions: AutoFixOptions;

  beforeEach(() => {
    engine = new AutoFixEngine();
    defaultOptions = {
      dryRun: true,
      maxIterations: 5,
      confidenceThreshold: 0.7,
      backupOriginals: true,
      outputDir: '.ae/test-auto-fix',
    };
  });

  describe('Analysis', () => {
    it('should analyze failure patterns', async () => {
      const failures = [
        FailureArtifactFactory.create({
          title: 'Contract Violation 1',
          category: 'contract_violation',
          severity: 'critical',
        }),
        FailureArtifactFactory.create({
          title: 'Contract Violation 2',
          category: 'contract_violation',
          severity: 'major',
        }),
        FailureArtifactFactory.create({
          title: 'Test Failure 1',
          category: 'test_failure',
          severity: 'minor',
        }),
      ];

      const result = await engine.analyzeFailures(failures, defaultOptions);

      expect(result.analysis).toContain('Total Failures');
      expect(result.analysis).toContain('contract_violation');
      expect(result.analysis).toContain('test_failure');
      expect(result.proposedFixes).toBeDefined();
      expect(result.riskAssessment).toContain('Risk Assessment');
    });

    it('should detect failure patterns', async () => {
      const failures = Array.from({ length: 5 }, (_, i) =>
        FailureArtifactFactory.create({
          title: `Contract Violation ${i + 1}`,
          category: 'contract_violation',
          severity: 'critical',
          location: {
            file: i < 3 ? 'src/auth.ts' : 'src/user.ts',
            line: 10 + i,
          },
        })
      );

      const result = await engine.analyzeFailures(failures, defaultOptions);

      expect(result.analysis).toContain('High frequency of contract_violation');
      expect(result.analysis).toContain('Multiple contract_violation failures in src/auth.ts');
    });

    it('should propose fixes based on confidence threshold', async () => {
      const failure = FailureArtifactFactory.create({
        title: 'High Confidence Fix',
        category: 'contract_violation',
        severity: 'critical',
        suggestedActions: [
          {
            type: 'spec_update',
            description: 'High confidence fix',
            confidence: 0.9,
          },
          {
            type: 'code_change',
            description: 'Low confidence fix',
            confidence: 0.5,
          },
        ],
      });

      const result = await engine.analyzeFailures([failure], {
        ...defaultOptions,
        confidenceThreshold: 0.7,
      });

      expect(result.proposedFixes).toHaveLength(1);
      expect(result.proposedFixes[0].description).toBe('High confidence fix');
    });
  });

  describe('Fix Execution', () => {
    it('should execute fixes in dry-run mode', async () => {
      const failures = [
        FailureArtifactFactory.create({
          title: 'Test Contract Violation',
          category: 'contract_violation',
          severity: 'critical',
          suggestedActions: [
            {
              type: 'spec_update',
              description: 'Update contract specification',
              confidence: 0.9,
            },
          ],
        }),
      ];

      const result = await engine.executeFixes(failures, {
        ...defaultOptions,
        dryRun: true,
      });

      expect(result.success).toBe(true);
      expect(result.appliedActions).toHaveLength(1);
      expect(result.appliedActions[0].description).toBe('Update contract specification');
      expect(result.generatedFiles).toHaveLength(0); // Dry run shouldn't generate files
    });

    it('should respect maximum iterations', async () => {
      const failures = Array.from({ length: 10 }, (_, i) =>
        FailureArtifactFactory.create({
          title: `Failure ${i + 1}`,
          category: 'contract_violation',
          severity: 'critical',
          suggestedActions: [
            {
              type: 'spec_update',
              description: `Fix ${i + 1}`,
              confidence: 0.9,
            },
          ],
        })
      );

      const result = await engine.executeFixes(failures, {
        ...defaultOptions,
        maxIterations: 3,
      });

      expect(result.appliedActions.length).toBeLessThanOrEqual(3);
      expect(result.recommendations.some(r => r.includes('maximum iterations'))).toBe(true);
    });

    it('should filter by confidence threshold', async () => {
      const failure = FailureArtifactFactory.create({
        title: 'Mixed Confidence Actions',
        category: 'contract_violation',
        severity: 'critical',
        suggestedActions: [
          {
            type: 'spec_update',
            description: 'High confidence action',
            confidence: 0.9,
          },
          {
            type: 'code_change',
            description: 'Low confidence action',
            confidence: 0.5,
          },
        ],
      });

      const result = await engine.executeFixes([failure], {
        ...defaultOptions,
        confidenceThreshold: 0.8,
      });

      expect(result.appliedActions).toHaveLength(1);
      expect(result.appliedActions[0].description).toBe('High confidence action');
    });

    it('should prioritize failures by severity', async () => {
      const failures = [
        FailureArtifactFactory.create({
          title: 'Minor Issue',
          category: 'test_failure',
          severity: 'minor',
          suggestedActions: [
            {
              type: 'test_update',
              description: 'Minor fix',
              confidence: 0.9,
            },
          ],
        }),
        FailureArtifactFactory.create({
          title: 'Critical Issue',
          category: 'contract_violation',
          severity: 'critical',
          suggestedActions: [
            {
              type: 'spec_update',
              description: 'Critical fix',
              confidence: 0.9,
            },
          ],
        }),
      ];

      const result = await engine.executeFixes(failures, defaultOptions);

      // Critical issue should be processed first
      expect(result.appliedActions[0].description).toBe('Critical fix');
      expect(result.appliedActions[1].description).toBe('Minor fix');
    });
  });

  describe('Strategy Registration', () => {
    it('should allow custom strategy registration', () => {
      const customStrategy: FixStrategy = {
        category: 'performance_regression',
        severity: ['major', 'critical'],
        minConfidence: 0.8,
        async execute(artifact, options) {
          return {
            success: true,
            appliedActions: [artifact.suggestedActions[0]],
            errors: [],
            generatedFiles: [],
            backupFiles: [],
            recommendations: ['Custom strategy executed'],
          };
        },
      };

      engine.registerStrategy(customStrategy);

      // Strategy should now be available for performance_regression failures
      expect(() => engine.registerStrategy(customStrategy)).not.toThrow();
    });

    it('should handle unsupported failure categories', async () => {
      const failure = FailureArtifactFactory.create({
        title: 'Unsupported Category',
        category: 'quality_gate_failure', // No default strategy for this
        severity: 'major',
        suggestedActions: [
          {
            type: 'config_change',
            description: 'Update quality gates',
            confidence: 0.9,
          },
        ],
      });

      const result = await engine.executeFixes([failure], defaultOptions);

      expect(result.success).toBe(false);
      expect(result.errors[0]).toContain('No strategy found');
    });

    it('should handle unsupported severity levels', async () => {
      const failure = FailureArtifactFactory.create({
        title: 'Info Level Contract Violation',
        category: 'contract_violation',
        severity: 'info', // Contract strategy doesn't support 'info' severity
        suggestedActions: [
          {
            type: 'spec_update',
            description: 'Update contract',
            confidence: 0.9,
          },
        ],
      });

      const result = await engine.executeFixes([failure], defaultOptions);

      expect(result.success).toBe(false);
      expect(result.recommendations[0]).toContain('does not support info severity');
    });
  });

  describe('Fix History', () => {
    it('should track fix history', async () => {
      const failure = FailureArtifactFactory.create({
        title: 'Test for History',
        category: 'contract_violation',
        severity: 'critical',
        suggestedActions: [
          {
            type: 'spec_update',
            description: 'Update spec',
            confidence: 0.9,
          },
        ],
      });

      expect(engine.getFixHistory()).toHaveLength(0);

      await engine.executeFixes([failure], defaultOptions);

      const history = engine.getFixHistory();
      expect(history).toHaveLength(1);
      expect(history[0].appliedActions).toHaveLength(1);
    });

    it('should clear fix history', async () => {
      const failure = FailureArtifactFactory.create({
        title: 'Test for Clear History',
        category: 'contract_violation',
        severity: 'critical',
        suggestedActions: [
          {
            type: 'spec_update',
            description: 'Update spec',
            confidence: 0.9,
          },
        ],
      });

      await engine.executeFixes([failure], defaultOptions);
      expect(engine.getFixHistory()).toHaveLength(1);

      engine.clearFixHistory();
      expect(engine.getFixHistory()).toHaveLength(0);
    });
  });

  describe('Error Handling', () => {
    it('should handle invalid failure artifacts gracefully', async () => {
      // Mock a failure that would cause strategy execution to throw
      const failure = FailureArtifactFactory.create({
        title: 'Problematic Failure',
        category: 'contract_violation',
        severity: 'critical',
        suggestedActions: [
          {
            type: 'spec_update',
            description: 'This will cause an error',
            confidence: 0.9,
          },
        ],
      });

      // Execute with very strict options that might cause issues
      const result = await engine.executeFixes([failure], {
        ...defaultOptions,
        confidenceThreshold: 2.0, // Invalid threshold > 1
      });

      // Should still complete, but with no applied actions
      expect(result.appliedActions).toHaveLength(0);
      expect(result.recommendations.length).toBeGreaterThan(0);
    });

    it('should handle collection format input', async () => {
      const collection = {
        failures: [
          FailureArtifactFactory.create({
            title: 'Collection Test',
            category: 'contract_violation',
            severity: 'critical',
            suggestedActions: [
              {
                type: 'spec_update',
                description: 'Fix from collection',
                confidence: 0.9,
              },
            ],
          }),
        ],
        metadata: {
          generatedAt: new Date().toISOString(),
          totalCount: 1,
          environment: 'test',
        },
        schemaVersion: '1.0.0',
      };

      const result = await engine.executeFixes(collection, defaultOptions);

      expect(result.success).toBe(true);
      expect(result.appliedActions).toHaveLength(1);
    });
  });
});