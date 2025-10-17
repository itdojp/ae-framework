/**
 * Tests for Runtime Middleware
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { z } from 'zod';
import {
  ExpressConformanceMiddleware,
  MiddlewareRegistry,
  OpenAPIConformanceIntegration,
} from '../../src/runtime/runtime-middleware.js';

// Mock OpenTelemetry
vi.mock('@opentelemetry/api', () => ({
  trace: {
    getTracer: () => ({
      startSpan: () => ({
        setStatus: vi.fn(),
        setAttributes: vi.fn(),
        recordException: vi.fn(),
        end: vi.fn(),
      }),
    }),
  },
  SpanStatusCode: {
    OK: 1,
    ERROR: 2,
  },
}));

// Mock Express types
interface MockRequest {
  body?: any;
  query?: any;
  params?: any;
  method: string;
  path: string;
  originalUrl?: string;
  route?: { path: string };
  headers: Record<string, string>;
  ip?: string;
  user?: { id: string };
  get(header: string): string | undefined;
}

interface MockResponse {
  status: vi.Mock;
  json: vi.Mock;
  send: vi.Mock;
  statusCode: number;
}

describe('ExpressConformanceMiddleware', () => {
  let middleware: ExpressConformanceMiddleware;
  let mockReq: MockRequest;
  let mockRes: MockResponse;
  let mockNext: vi.Mock;

  const userSchema = z.object({
    name: z.string().min(1),
    email: z.string().email(),
    age: z.number().min(0).max(150),
  });

  beforeEach(() => {
    middleware = new ExpressConformanceMiddleware({
      enabled: true,
      strictMode: false,
      logErrors: false, // Disable for cleaner test output
      generateArtifacts: false,
      includeRequestInfo: true,
    });

    mockReq = {
      method: 'POST',
      path: '/api/users',
      originalUrl: '/api/users',
      headers: {
        'x-request-id': 'req-123',
        'user-agent': 'test-agent',
      },
      ip: '127.0.0.1',
      get: vi.fn((header: string) => mockReq.headers[header.toLowerCase()]),
    };

    mockRes = {
      status: vi.fn().mockReturnThis(),
      json: vi.fn().mockReturnThis(),
      send: vi.fn().mockReturnThis(),
      statusCode: 200,
    };

    mockNext = vi.fn();
  });

  describe('Request Body Validation', () => {
    it('should validate valid request body', async () => {
      const validUser = {
        name: 'John Doe',
        email: 'john@example.com',
        age: 30,
      };

      mockReq.body = validUser;

      const validator = middleware.validateRequestBody(userSchema, 'createUser');
      await validator(mockReq as any, mockRes as any, mockNext);

      expect(mockNext).toHaveBeenCalledOnce();
      expect(mockRes.status).not.toHaveBeenCalled();
      expect(mockReq.body).toEqual(validUser);
    });

    it('should handle invalid request body in non-strict mode', async () => {
      const invalidUser = {
        name: '',
        email: 'invalid-email',
        age: -5,
      };

      mockReq.body = invalidUser;

      const validator = middleware.validateRequestBody(userSchema, 'createUser');
      await validator(mockReq as any, mockRes as any, mockNext);

      // In non-strict mode, should continue despite validation errors
      expect(mockNext).toHaveBeenCalledOnce();
      expect(mockRes.status).not.toHaveBeenCalled();
    });

    it('should reject invalid request body in strict mode', async () => {
      middleware = new ExpressConformanceMiddleware({
        enabled: true,
        strictMode: true,
        logErrors: false,
        generateArtifacts: false,
      });

      const invalidUser = {
        name: '',
        email: 'invalid-email',
        age: -5,
      };

      mockReq.body = invalidUser;

      const validator = middleware.validateRequestBody(userSchema, 'createUser');
      await validator(mockReq as any, mockRes as any, mockNext);

      expect(mockRes.status).toHaveBeenCalledWith(400);
      expect(mockRes.json).toHaveBeenCalledWith(
        expect.objectContaining({
          error: 'Validation Failed',
          message: 'request_body validation failed',
          details: expect.any(Array),
        })
      );
      expect(mockNext).not.toHaveBeenCalled();
    });

    it('should handle validation middleware errors', async () => {
      // Create a schema that will throw during validation
      const problematicSchema = {
        safeParse: vi.fn().mockImplementation(() => {
          throw new Error('Schema processing error');
        }),
      };

      mockReq.body = { test: 'data' };

      const validator = middleware.validateRequestBody(problematicSchema as any, 'test');
      await validator(mockReq as any, mockRes as any, mockNext);

      // Should continue in non-strict mode even with errors
      expect(mockNext).toHaveBeenCalledOnce();
    });
  });

  describe('Query Parameter Validation', () => {
    const querySchema = z.object({
      page: z.string().regex(/^\d+$/).transform(Number),
      limit: z.string().regex(/^\d+$/).transform(Number),
      search: z.string().optional(),
    });

    it('should validate valid query parameters', async () => {
      mockReq.query = {
        page: '1',
        limit: '10',
        search: 'test',
      };

      const validator = middleware.validateQueryParams(querySchema, 'listUsers');
      await validator(mockReq as any, mockRes as any, mockNext);

      expect(mockNext).toHaveBeenCalledOnce();
      expect(mockReq.query).toEqual({
        page: 1,
        limit: 10,
        search: 'test',
      });
    });

    it('should handle invalid query parameters', async () => {
      mockReq.query = {
        page: 'invalid',
        limit: 'also-invalid',
      };

      const validator = middleware.validateQueryParams(querySchema, 'listUsers');
      await validator(mockReq as any, mockRes as any, mockNext);

      // Should continue in non-strict mode
      expect(mockNext).toHaveBeenCalledOnce();
    });
  });

  describe('Path Parameter Validation', () => {
    const paramsSchema = z.object({
      id: z.string().regex(/^\d+$/).transform(Number),
      slug: z.string().min(1),
    });

    it('should validate valid path parameters', async () => {
      mockReq.params = {
        id: '123',
        slug: 'test-slug',
      };

      const validator = middleware.validatePathParams(paramsSchema, 'getUser');
      await validator(mockReq as any, mockRes as any, mockNext);

      expect(mockNext).toHaveBeenCalledOnce();
      expect(mockReq.params).toEqual({
        id: 123,
        slug: 'test-slug',
      });
    });

    it('should handle invalid path parameters', async () => {
      mockReq.params = {
        id: 'invalid',
        slug: '',
      };

      const validator = middleware.validatePathParams(paramsSchema, 'getUser');
      await validator(mockReq as any, mockRes as any, mockNext);

      // Should continue in non-strict mode
      expect(mockNext).toHaveBeenCalledOnce();
    });
  });

  describe('Response Validation', () => {
    const responseSchema = z.object({
      id: z.number(),
      name: z.string(),
      email: z.string().email(),
    });

    it('should validate response data', async () => {
      const validator = middleware.validateResponse(responseSchema, 'getUser');
      
      // Mock the response methods
      const originalSend = mockRes.send;
      const originalJson = mockRes.json;

      validator(mockReq as any, mockRes as any, mockNext);

      expect(mockNext).toHaveBeenCalledOnce();

      // Test that response methods are intercepted
      expect(mockRes.send).not.toBe(originalSend);
      expect(mockRes.json).not.toBe(originalJson);

      // Test valid response
      const validResponse = {
        id: 1,
        name: 'John Doe',
        email: 'john@example.com',
      };

      await (mockRes.json as any)(validResponse);
      // Should not throw or cause issues
    });

    it('should handle invalid response data gracefully', async () => {
      const validator = middleware.validateResponse(responseSchema, 'getUser');
      
      validator(mockReq as any, mockRes as any, mockNext);

      // Test invalid response
      const invalidResponse = {
        id: 'invalid',
        name: '',
        email: 'invalid-email',
      };

      // Should not throw even with invalid response
      expect(() => (mockRes.json as any)(invalidResponse)).not.toThrow();
    });
  });

  describe('Combined Validation', () => {
    it('should handle combined request/response validation', () => {
      const requestSchema = z.object({ name: z.string() });
      const responseSchema = z.object({ id: z.number(), name: z.string() });

      const validators = middleware.validate(
        requestSchema,
        responseSchema,
        'createUser',
        'body'
      );

      expect(validators).toHaveLength(2);
      expect(typeof validators[0]).toBe('function');
      expect(typeof validators[1]).toBe('function');
    });

    it('should handle partial validation (request only)', () => {
      const requestSchema = z.object({ name: z.string() });

      const validators = middleware.validate(
        requestSchema,
        null,
        'createUser',
        'body'
      );

      expect(validators).toHaveLength(1);
    });

    it('should handle partial validation (response only)', () => {
      const responseSchema = z.object({ id: z.number() });

      const validators = middleware.validate(
        null,
        responseSchema,
        'getUser'
      );

      expect(validators).toHaveLength(1);
    });
  });

  describe('Custom Error Handler', () => {
    it('should use custom error handler when provided', async () => {
      const customErrorHandler = vi.fn();
      
      middleware = new ExpressConformanceMiddleware({
        enabled: true,
        strictMode: true,
        customErrorHandler,
        logErrors: false,
        generateArtifacts: false,
      });

      const invalidUser = {
        name: '',
        email: 'invalid',
      };

      mockReq.body = invalidUser;

      const validator = middleware.validateRequestBody(userSchema, 'createUser');
      await validator(mockReq as any, mockRes as any, mockNext);

      expect(customErrorHandler).toHaveBeenCalledWith(
        expect.objectContaining({
          error: 'Validation Failed',
          details: expect.any(Array),
        }),
        mockReq,
        mockRes
      );
    });
  });

  describe('Disabled Middleware', () => {
    it('should skip validation when disabled', async () => {
      middleware = new ExpressConformanceMiddleware({
        enabled: false,
      });

      mockReq.body = { invalid: 'data' };

      const validator = middleware.validateRequestBody(userSchema, 'test');
      await validator(mockReq as any, mockRes as any, mockNext);

      expect(mockNext).toHaveBeenCalledOnce();
      expect(mockRes.status).not.toHaveBeenCalled();
    });
  });
});

describe('MiddlewareRegistry', () => {
  let registry: MiddlewareRegistry;

  beforeEach(() => {
    registry = new MiddlewareRegistry({
      enabled: true,
      strictMode: false,
      logErrors: false,
      generateArtifacts: false,
    });
  });

  describe('Route Registration', () => {
    it('should register route with validation schemas', () => {
      const schemas = {
        request: z.object({ name: z.string() }),
        response: z.object({ id: z.number(), name: z.string() }),
        query: z.object({ include: z.string().optional() }),
        params: z.object({ id: z.string() }),
      };

      const middlewares = registry.registerRoute(
        '/api/users/:id',
        'PUT',
        'updateUser',
        schemas
      );

      expect(middlewares).toHaveLength(4); // All schema types provided
      expect(middlewares.every(m => typeof m === 'function')).toBe(true);
    });

    it('should register route with partial schemas', () => {
      const schemas = {
        request: z.object({ name: z.string() }),
        response: z.object({ id: z.number() }),
      };

      const middlewares = registry.registerRoute(
        '/api/users',
        'POST',
        'createUser',
        schemas
      );

      expect(middlewares).toHaveLength(2); // Only request and response
    });

    it('should retrieve middleware for registered route', () => {
      const schemas = {
        request: z.object({ name: z.string() }),
      };

      registry.registerRoute('/api/users', 'POST', 'createUser', schemas);

      const middlewares = registry.getMiddleware('/api/users', 'POST');
      expect(middlewares).toHaveLength(1);
    });

    it('should return empty array for unregistered route', () => {
      const middlewares = registry.getMiddleware('/api/unknown', 'GET');
      expect(middlewares).toHaveLength(0);
    });

    it('should list all registered routes', () => {
      registry.registerRoute('/api/users', 'POST', 'createUser', {
        request: z.object({ name: z.string() }),
      });

      registry.registerRoute('/api/users/:id', 'GET', 'getUser', {
        response: z.object({ id: z.number() }),
      });

      const routes = registry.listRoutes();
      expect(routes).toHaveLength(2);
      expect(routes).toContainEqual({
        path: '/api/users',
        method: 'POST',
        operationId: 'createUser',
      });
      expect(routes).toContainEqual({
        path: '/api/users/:id',
        method: 'GET',
        operationId: 'getUser',
      });
    });
  });

  describe('Singleton Behavior', () => {
    it('should maintain singleton behavior', () => {
      const registry1 = MiddlewareRegistry.getInstance();
      const registry2 = MiddlewareRegistry.getInstance();

      expect(registry1).toBe(registry2);
    });
  });
});

describe('OpenAPIConformanceIntegration', () => {
  let integration: OpenAPIConformanceIntegration;

  beforeEach(() => {
    integration = new OpenAPIConformanceIntegration({
      enabled: true,
      strictMode: false,
      logErrors: false,
      generateArtifacts: false,
    });
  });

  describe('Middleware Generation', () => {
    it('should generate middleware from OpenAPI operation', () => {
      const operation = {
        operationId: 'createUser',
        requestBody: {
          schema: z.object({
            name: z.string(),
            email: z.string().email(),
          }),
        },
        parameters: [
          {
            schema: z.string(),
            in: 'query' as const,
          },
          {
            schema: z.string(),
            in: 'path' as const,
          },
        ],
        responses: {
          '200': {
            schema: z.object({
              id: z.number(),
              name: z.string(),
            }),
          },
        },
      };

      const middlewares = integration.generateMiddleware(operation);

      // Should generate middleware for: requestBody, query params, path params, response
      expect(middlewares.length).toBeGreaterThan(0);
      expect(middlewares.every(m => typeof m === 'function')).toBe(true);
    });

    it('should handle operation with minimal schemas', () => {
      const operation = {
        operationId: 'getUsers',
        responses: {
          '200': {
            schema: z.array(z.object({
              id: z.number(),
              name: z.string(),
            })),
          },
        },
      };

      const middlewares = integration.generateMiddleware(operation);

      expect(middlewares.length).toBeGreaterThan(0);
    });

    it('should handle operation with no schemas', () => {
      const operation = {
        operationId: 'healthCheck',
      };

      const middlewares = integration.generateMiddleware(operation);

      // Should still return middleware functions, even if they're no-ops
      expect(Array.isArray(middlewares)).toBe(true);
    });
  });
});

describe('Error Edge Cases', () => {
  let middleware: ExpressConformanceMiddleware;
  let mockReq: MockRequest;
  let mockRes: MockResponse;
  let mockNext: vi.Mock;

  beforeEach(() => {
    middleware = new ExpressConformanceMiddleware({
      enabled: true,
      strictMode: false,
      logErrors: false,
      generateArtifacts: false,
    });

    mockReq = {
      method: 'POST',
      path: '/api/test',
      headers: {},
      get: vi.fn(),
    };

    mockRes = {
      status: vi.fn().mockReturnThis(),
      json: vi.fn().mockReturnThis(),
      send: vi.fn().mockReturnThis(),
      statusCode: 200,
    };

    mockNext = vi.fn();
  });

  it('should handle extremely large request bodies', async () => {
    const largeObject = {
      data: Array.from({ length: 10000 }, (_, i) => ({
        id: i,
        value: `item-${i}`,
        metadata: {
          created: new Date().toISOString(),
          tags: [`tag-${i}`, `category-${i % 10}`],
        },
      })),
    };

    const schema = z.object({
      data: z.array(z.object({
        id: z.number(),
        value: z.string(),
        metadata: z.object({
          created: z.string(),
          tags: z.array(z.string()),
        }),
      })),
    });

    mockReq.body = largeObject;

    const validator = middleware.validateRequestBody(schema, 'largeBatch');
    
    // Should handle large objects without timing out or crashing
    await expect(
      validator(mockReq as any, mockRes as any, mockNext)
    ).resolves.not.toThrow();

    expect(mockNext).toHaveBeenCalledOnce();
  });

  it('should handle circular references gracefully', async () => {
    const circularObj: any = { name: 'test' };
    circularObj.self = circularObj;

    mockReq.body = circularObj;

    const schema = z.object({
      name: z.string(),
    });

    const validator = middleware.validateRequestBody(schema, 'circular');
    
    // Should handle circular references without infinite loops
    await expect(
      validator(mockReq as any, mockRes as any, mockNext)
    ).resolves.not.toThrow();
  });

  it('should handle null and undefined request data', async () => {
    const schema = z.object({
      name: z.string(),
    });

    const validator = middleware.validateRequestBody(schema, 'nullTest');

    // Test null body
    mockReq.body = null;
    await validator(mockReq as any, mockRes as any, mockNext);
    expect(mockNext).toHaveBeenCalled();

    mockNext.mockClear();

    // Test undefined body
    mockReq.body = undefined;
    await validator(mockReq as any, mockRes as any, mockNext);
    expect(mockNext).toHaveBeenCalled();
  });
});