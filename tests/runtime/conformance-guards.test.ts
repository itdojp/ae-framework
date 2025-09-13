/**
 * Tests for Runtime Conformance Guards
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { z } from 'zod';
// Mock OpenTelemetry
vi.mock('@opentelemetry/api', () => ({
  trace: {
    getTracer: () => ({
      startSpan: () => ({
        setStatus: () => {},
        setAttributes: () => {},
        recordException: () => {},
        end: () => {},
      }),
    }),
  },
  metrics: {
    getMeter: () => ({
      createCounter: () => ({
        add: () => {},
      }),
      createHistogram: () => ({
        record: () => {},
      }),
    }),
  },
}));

import {
  ConformanceGuard,
  ConformanceViolationError,
  GuardFactory,
  ConformanceRegistry,
  ValidateInput,
  ValidateOutput,
} from '../../src/runtime/conformance-guards.js';

describe('ConformanceGuard', () => {
  const userSchema = z.object({
    id: z.number(),
    name: z.string(),
    email: z.string().email(),
    age: z.number().min(0).max(150),
  });

  let guard: ConformanceGuard<any>;

  beforeEach(() => {
    guard = new ConformanceGuard(userSchema, 'user-schema', {
      enabled: true,
      failOnViolation: false,
      logViolations: false, // Disable for cleaner test output
      generateArtifacts: false, // Disable for testing
      telemetryEnabled: false, // Disable for testing
    });
  });

  describe('Input Validation', () => {
    it('should validate correct input data', async () => {
      const validUser = {
        id: 1,
        name: 'John Doe',
        email: 'john@example.com',
        age: 30,
      };

      const result = await guard.validateInput(validUser);

      expect(result.success).toBe(true);
      expect(result.data).toEqual(validUser);
      expect(result.errors).toHaveLength(0);
      expect(result.warnings).toHaveLength(0);
    });

    it('should reject invalid input data', async () => {
      const invalidUser = {
        id: 'not-a-number',
        name: '',
        email: 'invalid-email',
        age: -5,
      };

      const result = await guard.validateInput(invalidUser);

      expect(result.success).toBe(false);
      expect(result.data).toBeUndefined();
      expect(result.errors.length).toBeGreaterThan(0);
      expect(result.errors.some(err => err.includes('id'))).toBe(true);
      expect(result.errors.some(err => err.includes('email'))).toBe(true);
    });

    it('should handle missing required fields', async () => {
      const incompleteUser = {
        name: 'John Doe',
        // Missing id, email, age
      };

      const result = await guard.validateInput(incompleteUser);

      expect(result.success).toBe(false);
      expect(result.errors.some(err => err.includes('id'))).toBe(true);
      expect(result.errors.some(err => err.includes('email'))).toBe(true);
      expect(result.errors.some(err => err.includes('age'))).toBe(true);
    });

    it('should provide context in metadata', async () => {
      const context = {
        requestId: 'req-123',
        userId: 'user-456',
      };

      const result = await guard.validateInput({ id: 1, name: 'Test', email: 'test@example.com', age: 25 }, context);

      expect(result.metadata.context).toEqual(expect.objectContaining(context));
      expect(result.metadata.schemaName).toBe('user-schema');
      expect(result.metadata.timestamp).toBeDefined();
      expect(result.metadata.duration).toBeTypeOf('number');
    });
  });

  describe('Output Validation', () => {
    it('should validate correct output data', async () => {
      const validUser = {
        id: 1,
        name: 'John Doe',
        email: 'john@example.com',
        age: 30,
      };

      const result = await guard.validateOutput(validUser);

      expect(result.success).toBe(true);
      expect(result.data).toEqual(validUser);
    });

    it('should handle invalid output data', async () => {
      const invalidUser = {
        id: 1,
        name: 'John Doe',
        email: 'invalid-email',
        age: 200, // Too old
      };

      const result = await guard.validateOutput(invalidUser);

      expect(result.success).toBe(false);
      expect(result.errors.some(err => err.includes('email'))).toBe(true);
      expect(result.errors.some(err => err.includes('age'))).toBe(true);
    });
  });

  describe('Configuration', () => {
    it('should respect disabled configuration', async () => {
      guard.updateConfig({ enabled: false });

      const invalidData = { invalid: 'data' };
      const result = await guard.validateInput(invalidData);

      expect(result.success).toBe(true);
      expect(result.warnings).toContain('Conformance checking is disabled');
    });

    it('should fail on violation when configured', async () => {
      guard.updateConfig({ failOnViolation: true });

      const invalidUser = {
        id: 'invalid',
        name: 'Test',
        email: 'test@example.com',
        age: 25,
      };

      await expect(guard.validateInput(invalidUser)).rejects.toThrow(ConformanceViolationError);
    });

    it('should update and get configuration', () => {
      const newConfig = {
        enabled: false,
        failOnViolation: true,
        logViolations: false,
      };

      guard.updateConfig(newConfig);
      const config = guard.getConfig();

      expect(config.enabled).toBe(false);
      expect(config.failOnViolation).toBe(true);
      expect(config.logViolations).toBe(false);
      expect(config.generateArtifacts).toBeDefined(); // Should retain other config
    });
  });

  describe('Error Handling', () => {
    it('should create ConformanceViolationError with proper details', async () => {
      guard.updateConfig({ failOnViolation: true });

      const invalidData = { id: 'invalid' };

      try {
        await guard.validateInput(invalidData);
        fail('Should have thrown ConformanceViolationError');
      } catch (error) {
        expect(error).toBeInstanceOf(ConformanceViolationError);
        expect((error as ConformanceViolationError).schemaName).toBe('user-schema');
        expect((error as ConformanceViolationError).direction).toBe('input');
        expect((error as ConformanceViolationError).validationErrors).toBeDefined();
        expect((error as ConformanceViolationError).data).toEqual(invalidData);
      }
    });
  });
});

describe('GuardFactory', () => {
  const testSchema = z.object({
    message: z.string(),
  });

  describe('API Guards', () => {
    it('should create API request guard with strict settings', () => {
      const guard = GuardFactory.apiRequest(testSchema, 'test-operation');
      const config = guard.getConfig();

      expect(config.failOnViolation).toBe(true);
      expect(config.logViolations).toBe(true);
      expect(config.generateArtifacts).toBe(true);
      expect(config.context?.type).toBe('api_request');
      expect(config.context?.operation).toBe('test-operation');
    });

    it('should create API response guard with lenient settings', () => {
      const guard = GuardFactory.apiResponse(testSchema, 'test-operation');
      const config = guard.getConfig();

      expect(config.failOnViolation).toBe(false);
      expect(config.logViolations).toBe(true);
      expect(config.generateArtifacts).toBe(true);
      expect(config.context?.type).toBe('api_response');
    });
  });

  describe('Database Guards', () => {
    it('should create database entity guard with strict settings', () => {
      const guard = GuardFactory.databaseEntity(testSchema, 'user');
      const config = guard.getConfig();

      expect(config.failOnViolation).toBe(true);
      expect(config.context?.type).toBe('database_entity');
      expect(config.context?.entity).toBe('user');
    });
  });

  describe('Configuration Guards', () => {
    it('should create configuration guard without artifacts', () => {
      const guard = GuardFactory.configuration(testSchema, 'app-config');
      const config = guard.getConfig();

      expect(config.failOnViolation).toBe(true);
      expect(config.generateArtifacts).toBe(false);
      expect(config.context?.type).toBe('configuration');
      expect(config.context?.config).toBe('app-config');
    });
  });

  describe('Event Guards', () => {
    it('should create event guard with lenient settings', () => {
      const guard = GuardFactory.event(testSchema, 'user-created');
      const config = guard.getConfig();

      expect(config.failOnViolation).toBe(false);
      expect(config.generateArtifacts).toBe(true);
      expect(config.context?.type).toBe('event');
      expect(config.context?.eventType).toBe('user-created');
    });
  });
});

describe('Decorators', () => {
  const nameSchema = z.string().min(1);
  const guard = new ConformanceGuard(nameSchema, 'name-schema', {
    failOnViolation: false,
    logViolations: false,
    generateArtifacts: false,
    telemetryEnabled: false,
  });

  class TestService {
    async processName(name: string): Promise<string> {
      return `Hello, ${name}!`;
    }

    async getName(): Promise<string> {
      return 'John Doe';
    }
  }

  // 手動でデコレータを適用（ESM/変換差異の影響を避ける）
  const inDesc = Object.getOwnPropertyDescriptor(TestService.prototype, 'processName')!;
  const outDesc = Object.getOwnPropertyDescriptor(TestService.prototype, 'getName')!;
  ValidateInput(guard)(TestService.prototype as any, 'processName', inDesc);
  ValidateOutput(guard)(TestService.prototype as any, 'getName', outDesc);

  let service: TestService;

  beforeEach(() => {
    service = new TestService();
  });

  describe('ValidateInput Decorator', () => {
    it('should validate input and proceed with valid data', async () => {
      const result = await service.processName('John');
      expect(result).toBe('Hello, John!');
    });

    it('should handle invalid input gracefully', async () => {
      const result = await service.processName('');
      // Should still proceed since failOnViolation is false
      expect(result).toBe('Hello, !');
    });

    it('should throw error when failOnViolation is true', async () => {
      guard.updateConfig({ failOnViolation: true });

      await expect(service.processName('')).rejects.toThrow(ConformanceViolationError);

      // Reset for other tests
      guard.updateConfig({ failOnViolation: false });
    });
  });

  describe('ValidateOutput Decorator', () => {
    it('should validate output and return data', async () => {
      const result = await service.getName();
      expect(result).toBe('John Doe');
    });
  });
});

describe('ConformanceRegistry', () => {
  let registry: ConformanceRegistry;

  beforeEach(() => {
    registry = ConformanceRegistry.getInstance();
    registry.clear(); // Clear any previous registrations
  });

  describe('Schema Registration', () => {
    it('should register and retrieve schemas', () => {
      const userSchema = z.object({
        name: z.string(),
        age: z.number(),
      });

      registry.registerSchema('user', userSchema);

      const retrieved = registry.getSchema('user');
      expect(retrieved).toBe(userSchema);
    });

    it('should list registered schemas', () => {
      registry.registerSchema('user', z.object({ name: z.string() }));
      registry.registerSchema('post', z.object({ title: z.string() }));

      const schemas = registry.listSchemas();
      expect(schemas).toContain('user');
      expect(schemas).toContain('post');
      expect(schemas).toHaveLength(2);
    });
  });

  describe('Guard Registration', () => {
    it('should register and retrieve guards', () => {
      const schema = z.object({ name: z.string() });
      const guard = new ConformanceGuard(schema, 'test-guard');

      registry.registerGuard('test-guard', guard);

      const retrieved = registry.getGuard('test-guard');
      expect(retrieved).toBe(guard);
    });

    it('should create guard from registered schema', () => {
      const schema = z.object({ name: z.string() });
      registry.registerSchema('user', schema);

      const guard = registry.createGuard('user', 'user-guard');

      expect(guard).toBeDefined();
      expect(guard?.getConfig().context).toBeDefined();
    });

    it('should return null for unknown schema', () => {
      const guard = registry.createGuard('unknown-schema');
      expect(guard).toBeNull();
    });

    it('should list registered guards', () => {
      const schema = z.object({ name: z.string() });
      const guard1 = new ConformanceGuard(schema, 'guard1');
      const guard2 = new ConformanceGuard(schema, 'guard2');

      registry.registerGuard('guard1', guard1);
      registry.registerGuard('guard2', guard2);

      const guards = registry.listGuards();
      expect(guards).toContain('guard1');
      expect(guards).toContain('guard2');
      expect(guards).toHaveLength(2);
    });
  });

  describe('Registry Management', () => {
    it('should clear all registrations', () => {
      registry.registerSchema('test', z.string());
      registry.registerGuard('test', new ConformanceGuard(z.string(), 'test'));

      expect(registry.listSchemas()).toHaveLength(1);
      expect(registry.listGuards()).toHaveLength(1);

      registry.clear();

      expect(registry.listSchemas()).toHaveLength(0);
      expect(registry.listGuards()).toHaveLength(0);
    });

    it('should maintain singleton behavior', () => {
      const registry1 = ConformanceRegistry.getInstance();
      const registry2 = ConformanceRegistry.getInstance();

      expect(registry1).toBe(registry2);
    });
  });
});

describe('Edge Cases and Error Handling', () => {
  const schema = z.object({
    name: z.string(),
    nested: z.object({
      value: z.number(),
    }),
  });

  let guard: ConformanceGuard<any>;

  beforeEach(() => {
    guard = new ConformanceGuard(schema, 'test-schema', {
      logViolations: false,
      generateArtifacts: false,
      telemetryEnabled: false,
    });
  });

  it('should handle nested validation errors', async () => {
    const invalidData = {
      name: 'test',
      nested: {
        value: 'not-a-number',
      },
    };

    const result = await guard.validateInput(invalidData);

    expect(result.success).toBe(false);
    expect(result.errors.some(err => err.includes('nested.value'))).toBe(true);
  });

  it('should handle null and undefined data', async () => {
    const nullResult = await guard.validateInput(null);
    const undefinedResult = await guard.validateInput(undefined);

    expect(nullResult.success).toBe(false);
    expect(undefinedResult.success).toBe(false);
  });

  it('should handle complex nested structures', async () => {
    const complexSchema = z.object({
      users: z.array(z.object({
        name: z.string(),
        permissions: z.record(z.boolean()),
      })),
      metadata: z.object({
        version: z.string(),
        features: z.array(z.string()),
      }),
    });

    const complexGuard = new ConformanceGuard(complexSchema, 'complex', {
      logViolations: false,
      generateArtifacts: false,
      telemetryEnabled: false,
    });

    const validData = {
      users: [
        {
          name: 'user1',
          permissions: { read: true, write: false },
        },
      ],
      metadata: {
        version: '1.0.0',
        features: ['feature1', 'feature2'],
      },
    };

    const result = await complexGuard.validateInput(validData);
    expect(result.success).toBe(true);
  });

  it('should handle very large objects gracefully', async () => {
    const largeObject = {
      name: 'test',
      nested: {
        value: 42,
      },
      // Add some bulk
      bulk: Array.from({ length: 1000 }, (_, i) => `item-${i}`),
    };

    const result = await guard.validateInput(largeObject);
    // Should either succeed or fail gracefully without performance issues
    expect(typeof result.success).toBe('boolean');
    expect(Array.isArray(result.errors)).toBe(true);
  });
});
