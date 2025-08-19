/**
 * Tests for CEGIS Failure Artifact Schema
 */

import { describe, it, expect } from 'vitest';
import {
  FailureArtifactSchema,
  FailureArtifactCollectionSchema,
  FailureArtifactFactory,
  validateFailureArtifact,
  validateFailureArtifactCollection,
  isFailureArtifact,
} from '../../src/cegis/failure-artifact-schema.js';

describe('FailureArtifact Schema', () => {
  describe('Basic Validation', () => {
    it('should validate a minimal failure artifact', () => {
      const artifact = {
        id: crypto.randomUUID(),
        title: 'Test Failure',
        description: 'A test failure description',
        severity: 'major',
        category: 'runtime_error',
        context: {
          timestamp: new Date().toISOString(),
          environment: 'test',
        },
        evidence: {},
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      };

      expect(() => FailureArtifactSchema.parse(artifact)).not.toThrow();
    });

    it('should reject invalid severity levels', () => {
      const artifact = {
        id: crypto.randomUUID(),
        title: 'Test Failure',
        description: 'A test failure description',
        severity: 'invalid',
        category: 'runtime_error',
        context: {
          timestamp: new Date().toISOString(),
          environment: 'test',
        },
        evidence: {},
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      };

      expect(() => FailureArtifactSchema.parse(artifact)).toThrow();
    });

    it('should reject invalid categories', () => {
      const artifact = {
        id: crypto.randomUUID(),
        title: 'Test Failure',
        description: 'A test failure description',
        severity: 'major',
        category: 'invalid_category',
        context: {
          timestamp: new Date().toISOString(),
          environment: 'test',
        },
        evidence: {},
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      };

      expect(() => FailureArtifactSchema.parse(artifact)).toThrow();
    });

    it('should validate complex failure artifact with all fields', () => {
      const artifact = {
        id: crypto.randomUUID(),
        title: 'Complex Test Failure',
        description: 'A comprehensive test failure with all fields',
        severity: 'critical',
        category: 'contract_violation',
        location: {
          file: '/src/test.ts',
          line: 42,
          column: 10,
          function: 'testFunction',
          module: 'testModule',
        },
        context: {
          environment: 'production',
          phase: 'testing',
          component: 'auth-service',
          timestamp: new Date().toISOString(),
          commitHash: 'abc123',
          branch: 'main',
          userId: 'user123',
        },
        evidence: {
          stackTrace: 'Error at line 42...',
          logs: ['Log entry 1', 'Log entry 2'],
          metrics: {
            responseTime: 150,
            memoryUsage: 85.5,
            isError: true,
          },
          screenshots: ['base64image1', 'base64image2'],
          networkLogs: [
            {
              url: 'https://api.example.com/users',
              method: 'POST',
              status: 400,
              requestBody: '{"email": "test"}',
              responseBody: '{"error": "Invalid email"}',
            },
          ],
          environmentInfo: {
            nodeVersion: '18.0.0',
            platform: 'linux',
          },
        },
        rootCause: {
          hypothesis: 'Email validation regex is incorrect',
          evidence: ['Failed regex test', 'Multiple user reports'],
          confidence: 0.85,
          relatedFailures: ['failure-id-1', 'failure-id-2'],
        },
        suggestedActions: [
          {
            type: 'code_change',
            description: 'Update email validation regex',
            targetFile: '/src/validators/email.ts',
            proposedChange: 'const emailRegex = /^[^\\s@]+@[^\\s@]+\\.[^\\s@]+$/;',
            confidence: 0.9,
            reasoning: 'Current regex is too restrictive',
            prerequisites: ['backup-current-file', 'run-tests'],
          },
        ],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        resolvedAt: new Date().toISOString(),
        tags: ['email', 'validation', 'critical'],
        parentFailureId: crypto.randomUUID(),
        childFailureIds: [crypto.randomUUID(), crypto.randomUUID()],
        status: 'analyzing',
        assignee: 'dev-team-lead',
        schemaVersion: '1.0.0',
      };

      expect(() => FailureArtifactSchema.parse(artifact)).not.toThrow();
    });
  });

  describe('FailureArtifactFactory', () => {
    it('should create basic failure artifact', () => {
      const artifact = FailureArtifactFactory.create({
        title: 'Factory Test',
        description: 'Test created by factory',
      });

      expect(artifact.id).toBeDefined();
      expect(artifact.title).toBe('Factory Test');
      expect(artifact.description).toBe('Test created by factory');
      expect(artifact.severity).toBe('minor');
      expect(artifact.category).toBe('runtime_error');
      expect(artifact.createdAt).toBeDefined();
      expect(artifact.updatedAt).toBeDefined();
    });

    it('should create from error', () => {
      const error = new Error('Test error message');
      error.stack = 'Error: Test error message\n    at test.js:10:5';
      
      const artifact = FailureArtifactFactory.fromError(error, {
        environment: 'test',
        component: 'test-component',
      });

      expect(artifact.title).toBe('Error');
      expect(artifact.description).toBe('Test error message');
      expect(artifact.severity).toBe('major');
      expect(artifact.category).toBe('runtime_error');
      expect(artifact.evidence.stackTrace).toBe(error.stack);
      expect(artifact.context.environment).toBe('test');
      expect(artifact.context.component).toBe('test-component');
    });

    it('should create from test failure', () => {
      const artifact = FailureArtifactFactory.fromTestFailure(
        'should validate user input',
        'Expected validation to pass but got error',
        { file: 'tests/user.test.ts', line: 25 }
      );

      expect(artifact.title).toBe('Test Failure: should validate user input');
      expect(artifact.description).toBe('Expected validation to pass but got error');
      expect(artifact.severity).toBe('major');
      expect(artifact.category).toBe('test_failure');
      expect(artifact.location?.file).toBe('tests/user.test.ts');
      expect(artifact.location?.line).toBe(25);
    });

    it('should create from contract violation', () => {
      const expected = { name: 'string', age: 'number' };
      const actual = { name: 'John', age: '25' };
      
      const artifact = FailureArtifactFactory.fromContractViolation(
        'UserProfile',
        expected,
        actual,
        { file: 'src/models/user.ts', line: 15 }
      );

      expect(artifact.title).toBe('Contract Violation: UserProfile');
      expect(artifact.description).toContain('Expected:');
      expect(artifact.description).toContain('Got:');
      expect(artifact.severity).toBe('critical');
      expect(artifact.category).toBe('contract_violation');
      expect(artifact.suggestedActions).toHaveLength(2);
      expect(artifact.suggestedActions[0].type).toBe('spec_update');
      expect(artifact.suggestedActions[1].type).toBe('code_change');
    });
  });

  describe('Collection Schema', () => {
    it('should validate failure artifact collection', () => {
      const collection = {
        failures: [
          FailureArtifactFactory.create({ title: 'Test 1' }),
          FailureArtifactFactory.create({ title: 'Test 2' }),
        ],
        metadata: {
          generatedAt: new Date().toISOString(),
          totalCount: 2,
          environment: 'test',
        },
        schemaVersion: '1.0.0',
      };

      expect(() => FailureArtifactCollectionSchema.parse(collection)).not.toThrow();
    });

    it('should validate collection with severity and category counts', () => {
      const collection = {
        failures: [
          FailureArtifactFactory.create({ title: 'Test 1', severity: 'critical' }),
          FailureArtifactFactory.create({ title: 'Test 2', severity: 'major' }),
        ],
        metadata: {
          generatedAt: new Date().toISOString(),
          totalCount: 2,
          severityCounts: { critical: 1, major: 1, minor: 0, info: 0 },
          categoryCounts: { runtime_error: 2 },
          environment: 'test',
        },
        schemaVersion: '1.0.0',
      };

      expect(() => FailureArtifactCollectionSchema.parse(collection)).not.toThrow();
    });
  });

  describe('Utility Functions', () => {
    it('should validate valid failure artifact', () => {
      const artifact = FailureArtifactFactory.create({ title: 'Test' });
      
      expect(() => validateFailureArtifact(artifact)).not.toThrow();
    });

    it('should throw on invalid failure artifact', () => {
      const invalidArtifact = { invalid: 'data' };
      
      expect(() => validateFailureArtifact(invalidArtifact)).toThrow();
    });

    it('should validate valid collection', () => {
      const collection = {
        failures: [FailureArtifactFactory.create({ title: 'Test' })],
        metadata: {
          generatedAt: new Date().toISOString(),
          totalCount: 1,
          environment: 'test',
        },
        schemaVersion: '1.0.0',
      };
      
      expect(() => validateFailureArtifactCollection(collection)).not.toThrow();
    });

    it('should identify valid failure artifacts with type guard', () => {
      const artifact = FailureArtifactFactory.create({ title: 'Test' });
      const invalidData = { invalid: 'data' };
      
      expect(isFailureArtifact(artifact)).toBe(true);
      expect(isFailureArtifact(invalidData)).toBe(false);
    });
  });

  describe('Edge Cases', () => {
    it('should handle minimum required fields', () => {
      const minimal = {
        id: crypto.randomUUID(),
        title: 'Min',
        description: 'Minimal',
        severity: 'info',
        category: 'runtime_error',
        context: {
          timestamp: new Date().toISOString(),
        },
        evidence: {},
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      };

      expect(() => FailureArtifactSchema.parse(minimal)).not.toThrow();
    });

    it('should apply default values correctly', () => {
      const artifact = FailureArtifactFactory.create({
        title: 'Test',
        description: 'Test description',
      });

      expect(artifact.severity).toBe('minor');
      expect(artifact.category).toBe('runtime_error');
      expect(artifact.status).toBe('open');
      expect(artifact.tags).toEqual([]);
      expect(artifact.suggestedActions).toEqual([]);
      expect(artifact.evidence.logs).toEqual([]);
      expect(artifact.evidence.screenshots).toEqual([]);
      expect(artifact.evidence.networkLogs).toEqual([]);
    });

    it('should validate datetime strings', () => {
      const artifact = FailureArtifactFactory.create({ title: 'Test' });
      
      // Should have valid ISO datetime strings
      expect(new Date(artifact.createdAt).toISOString()).toBe(artifact.createdAt);
      expect(new Date(artifact.updatedAt).toISOString()).toBe(artifact.updatedAt);
      expect(new Date(artifact.context.timestamp).toISOString()).toBe(artifact.context.timestamp);
    });

    it('should validate confidence values are between 0 and 1', () => {
      const invalidAction = {
        type: 'code_change',
        description: 'Test action',
        confidence: 1.5, // Invalid - greater than 1
      };

      expect(() => {
        FailureArtifactFactory.create({
          title: 'Test',
          description: 'Test',
          suggestedActions: [invalidAction],
        });
      }).toThrow();
    });
  });
});