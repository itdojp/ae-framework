/**
 * Runtime Conformance Middleware
 * 
 * Express and Fastify middleware for automatic runtime contract validation
 * with OpenTelemetry integration and failure artifact generation
 */

import type { FastifyRequest, FastifyReply, FastifyInstance } from 'fastify';
import { z, type ZodRawShape, type ZodTypeAny } from 'zod';
import { GuardFactory } from './conformance-guards.js';
import type { ConformanceResult } from './conformance-guards.js';
import { trace, SpanStatusCode } from '@opentelemetry/api';

/**
 * Minimal request/response types that remain compatible with Express but keep
 * the middleware free from `any` usage. Express itself remains an optional
 * dependency.
 */
interface ExpressRouteInfo {
  path?: string;
}

export interface ExpressRequestLike {
  method: string;
  path: string;
  route?: ExpressRouteInfo | null;
  body: unknown;
  query: unknown;
  params: unknown;
  headers?: Record<string, unknown>;
  get(name: string): string | undefined;
  ip?: string;
  user?: { id?: string } | null;
}

export interface ExpressResponseLike {
  status(code: number): ExpressResponseLike;
  json(payload: unknown): ExpressResponseLike;
  send(payload: unknown): ExpressResponseLike;
  statusCode: number;
}

export type ExpressNextFunction = (error?: unknown) => void;

type ExpressMiddleware = (
  req: ExpressRequestLike,
  res: ExpressResponseLike,
  next: ExpressNextFunction
) => void | Promise<void>;

type ResponseInvoker = (payload: unknown) => ExpressResponseLike;

const tracer = trace.getTracer('ae-framework-runtime-middleware');

// Middleware configuration
export interface MiddlewareConfig {
  enabled: boolean;
  strictMode: boolean; // Fail requests on validation errors
  logErrors: boolean;
  generateArtifacts: boolean;
  includeRequestInfo: boolean;
  customErrorHandler?: MiddlewareErrorHandler;
}

const defaultMiddlewareConfig: MiddlewareConfig = {
  enabled: true,
  strictMode: false,
  logErrors: true,
  generateArtifacts: true,
  includeRequestInfo: true,
};

// Validation context for middleware
interface ValidationContext extends Record<string, unknown> {
  operationId: string;
  method: string;
  path: string;
  timestamp: string;
  requestId?: string;
  userId?: string;
  userAgent?: string;
  ip?: string;
}

type MiddlewareErrorHandler = (
  error: unknown,
  req: ExpressRequestLike,
  res: ExpressResponseLike
) => void;

interface RuntimeValidationError {
  error: 'Validation Failed';
  message: string;
  details: string[];
  timestamp: string;
  path: string;
  method: string;
}

/**
 * Express Middleware Factory
 */
export class ExpressConformanceMiddleware {
  private config: MiddlewareConfig;

  constructor(config: Partial<MiddlewareConfig> = {}) {
    this.config = { ...defaultMiddlewareConfig, ...config };
  }

  /**
   * Validate request body
   */
  validateRequestBody<T>(schema: z.ZodSchema<T>, operationId: string) {
    const guard = GuardFactory.apiRequest(schema, operationId);
    // ミドルウェア側でstrict処理を行うため、ガードは非例外化
    guard.updateConfig({ failOnViolation: false });
    
    return async (req: ExpressRequestLike, res: ExpressResponseLike, next: ExpressNextFunction) => {
      if (!this.config.enabled) {
        return next();
      }

      const span = tracer.startSpan(`validate_request_body_${operationId}`);
      
      try {
        const context = this.createValidationContext(req, operationId);
        const result = await guard.validateInput(req.body, context);

        span.setAttributes({
          'http.method': req.method,
          'http.route': req.route?.path || req.path,
          'conformance.operation_id': operationId,
          'conformance.validation_result': result.success ? 'success' : 'failure',
        });

        if (!result.success) {
          return this.handleValidationError(result, req, res, next, 'request_body');
        }

        // Replace body with validated data
        if (result.data !== undefined) {
          req.body = result.data;
        }
        span.setStatus({ code: SpanStatusCode.OK });
        next();

      } catch (error) {
        span.recordException(error as Error);
        span.setStatus({ code: SpanStatusCode.ERROR });
        this.handleMiddlewareError(error, req, res, next);
      } finally {
        span.end();
      }
    };
  }

  /**
   * Validate query parameters
   */
  validateQueryParams<T>(schema: z.ZodSchema<T>, operationId: string) {
    const guard = GuardFactory.apiRequest(schema, `${operationId}_query`);
    guard.updateConfig({ failOnViolation: false });
    
    return async (req: ExpressRequestLike, res: ExpressResponseLike, next: ExpressNextFunction) => {
      if (!this.config.enabled) {
        return next();
      }

      const span = tracer.startSpan(`validate_query_params_${operationId}`);
      
      try {
        const context = this.createValidationContext(req, operationId);
        const result = await guard.validateInput(req.query, context);

        span.setAttributes({
          'http.method': req.method,
          'http.route': req.route?.path || req.path,
          'conformance.operation_id': operationId,
          'conformance.validation_result': result.success ? 'success' : 'failure',
        });

        if (!result.success) {
          return this.handleValidationError(result, req, res, next, 'query_params');
        }

        if (result.success && result.data !== undefined) {
          req.query = result.data;
        }
        span.setStatus({ code: SpanStatusCode.OK });
        next();

      } catch (error) {
        span.recordException(error as Error);
        span.setStatus({ code: SpanStatusCode.ERROR });
        this.handleMiddlewareError(error, req, res, next);
      } finally {
        span.end();
      }
    };
  }

  /**
   * Validate path parameters
   */
  validatePathParams<T>(schema: z.ZodSchema<T>, operationId: string) {
    const guard = GuardFactory.apiRequest(schema, `${operationId}_params`);
    guard.updateConfig({ failOnViolation: false });
    
    return async (req: ExpressRequestLike, res: ExpressResponseLike, next: ExpressNextFunction) => {
      if (!this.config.enabled) {
        return next();
      }

      const span = tracer.startSpan(`validate_path_params_${operationId}`);
      
      try {
        const context = this.createValidationContext(req, operationId);
        const result = await guard.validateInput(req.params, context);

        span.setAttributes({
          'http.method': req.method,
          'http.route': req.route?.path || req.path,
          'conformance.operation_id': operationId,
          'conformance.validation_result': result.success ? 'success' : 'failure',
        });

        if (!result.success) {
          return this.handleValidationError(result, req, res, next, 'path_params');
        }

        if (result.success && result.data !== undefined) {
          req.params = result.data;
        }
        span.setStatus({ code: SpanStatusCode.OK });
        next();

      } catch (error) {
        span.recordException(error as Error);
        span.setStatus({ code: SpanStatusCode.ERROR });
        this.handleMiddlewareError(error, req, res, next);
      } finally {
        span.end();
      }
    };
  }

  /**
   * Validate response data
   */
  validateResponse<T>(schema: z.ZodSchema<T>, operationId: string): ExpressMiddleware {
    const guard = GuardFactory.apiResponse(schema, operationId);
    
    return (req: ExpressRequestLike, res: ExpressResponseLike, next: ExpressNextFunction) => {
      if (!this.config.enabled) {
        next();
        return;
      }

      const validateAndSend = (payload: unknown, invoke: ResponseInvoker): ExpressResponseLike => {
        const span = tracer.startSpan(`validate_response_${operationId}`);
        span.setAttributes({
          'http.method': req.method,
          'http.route': req.route?.path || req.path,
          'conformance.operation_id': operationId,
          'http.status_code': res.statusCode,
        });

        const context = this.createValidationContext(req, operationId);

        void guard.validateOutput(payload, context)
          .then((result) => {
            span.setAttributes({
              'conformance.validation_result': result.success ? 'success' : 'failure',
            });

            if (!result.success && this.config.logErrors) {
              console.warn(`🚨 Response validation failed for ${operationId}:`, result.errors);
            }

            span.setStatus({
              code: result.success ? SpanStatusCode.OK : SpanStatusCode.ERROR,
            });
          })
          .catch((error) => {
            span.recordException(error as Error);
            span.setStatus({ code: SpanStatusCode.ERROR });

            if (this.config.logErrors) {
              console.error(`Response validation error for ${operationId}:`, error);
            }
          })
          .finally(() => {
            span.end();
          });

        return invoke(payload);
      };

      const originalSend = res.send.bind(res) as ResponseInvoker;
      res.send = ((payload: unknown) => validateAndSend(payload, originalSend)) as typeof res.send;

      const originalJson = res.json.bind(res) as ResponseInvoker;
      res.json = ((payload: unknown) => validateAndSend(payload, originalJson)) as typeof res.json;

      next();
    };
  }

  /**
   * Combined request/response validation middleware
   */
  validate<TReq, TRes>(
    requestSchema: z.ZodSchema<TReq> | null,
    responseSchema: z.ZodSchema<TRes> | null,
    operationId: string,
    target: 'body' | 'query' | 'params' = 'body'
  ) {
    const middlewares: Array<ExpressMiddleware | undefined> = [
      requestSchema ? (
        target === 'body' ? this.validateRequestBody(requestSchema, operationId) :
        target === 'query' ? this.validateQueryParams(requestSchema, operationId) :
        this.validatePathParams(requestSchema, operationId)
      ) : undefined,
      responseSchema ? this.validateResponse(responseSchema, operationId) : undefined,
    ];

    return middlewares.filter(
      (middleware): middleware is ExpressMiddleware => typeof middleware === 'function'
    );
  }

  private createValidationContext(req: ExpressRequestLike, operationId: string): ValidationContext {
    const context: ValidationContext = {
      operationId,
      method: req.method,
      path: req.path,
      timestamp: new Date().toISOString(),
    };

    if (this.config.includeRequestInfo) {
      const headers = req.headers ?? {};
      const requestIdHeader = headers['x-request-id'];
      if (typeof requestIdHeader === 'string') {
        context.requestId = requestIdHeader;
      } else if (Array.isArray(requestIdHeader)) {
        const stringId = requestIdHeader.find(
          (value): value is string => typeof value === 'string' && value.length > 0
        );
        if (stringId) {
          context.requestId = stringId;
        }
      }

      const userId = req.user?.id;
      if (typeof userId === 'string' && userId.length > 0) {
        context.userId = userId;
      }

      const userAgent = req.get('User-Agent');
      if (typeof userAgent === 'string' && userAgent.length > 0) {
        context.userAgent = userAgent;
      }

      if (typeof req.ip === 'string' && req.ip.length > 0) {
        context.ip = req.ip;
      }
    }

    return context;
  }

  private handleValidationError(
    result: ConformanceResult,
    req: ExpressRequestLike,
    res: ExpressResponseLike,
    next: ExpressNextFunction,
    target: string
  ): void {
    const error: RuntimeValidationError = {
      error: 'Validation Failed',
      message: `${target} validation failed`,
      details: result.errors,
      timestamp: result.metadata.timestamp,
      path: req.path,
      method: req.method,
    };

    if (this.config.customErrorHandler) {
      this.config.customErrorHandler(error, req, res);
      return;
    }

    if (this.config.strictMode) {
      res.status(400).json(error);
    } else {
      if (this.config.logErrors) {
        console.warn('Validation failed but continuing in non-strict mode:', error);
      }
      next();
    }
  }

  private handleMiddlewareError(
    error: unknown,
    req: ExpressRequestLike,
    res: ExpressResponseLike,
    next: ExpressNextFunction
  ): void {
    if (this.config.customErrorHandler) {
      this.config.customErrorHandler(error, req, res);
      return;
    }

    if (this.config.logErrors) {
      console.error('Conformance middleware error:', error);
    }

    if (this.config.strictMode) {
      res.status(500).json({
        error: 'Internal Validation Error',
        message: 'An error occurred during request validation',
        timestamp: new Date().toISOString(),
      });
    } else {
      next();
    }
  }
}

interface RegisteredRoute {
  operationId: string;
  middlewares: ExpressMiddleware[];
  schemas: {
    request?: z.ZodSchema<unknown>;
    response?: z.ZodSchema<unknown>;
    query?: z.ZodSchema<unknown>;
    params?: z.ZodSchema<unknown>;
  };
}

const extractOperationId = (request: FastifyRequest): string | undefined => {
  const candidate = (request as unknown as { routerMethod?: { operationId?: string } }).routerMethod;
  return candidate?.operationId;
};

/**
 * Fastify Plugin for Runtime Conformance
 */
export function fastifyConformancePlugin(
  fastify: FastifyInstance,
  options: {
    config?: Partial<MiddlewareConfig>;
    schemas?: Record<string, z.ZodSchema<unknown>>;
  } = {}
) {
  const config = { ...defaultMiddlewareConfig, ...options.config };
  const schemas = options.schemas ?? {};

  // Register schemas
  for (const [name, schema] of Object.entries(schemas)) {
    fastify.addSchema({
      $id: name,
      ...zodToJsonSchema(schema),
    });
  }

  // Add validation hook
  fastify.addHook('preHandler', (request: FastifyRequest) => {
    if (!config.enabled) return;

    const operationId = extractOperationId(request) ?? `${request.method}_${request.url}`;

    const span = tracer.startSpan(`fastify_validate_${operationId}`);

    try {
      span.setAttributes({
        'http.method': request.method,
        'http.url': request.url,
        'conformance.operation_id': operationId,
      });

      // Validation would be handled by Fastify's built-in JSON schema validation
      // This hook is mainly for telemetry and artifact generation

      span.setStatus({ code: SpanStatusCode.OK });

    } catch (error) {
      span.recordException(error as Error);
      span.setStatus({ code: SpanStatusCode.ERROR });
      throw error;
    } finally {
      span.end();
    }
  });

  // Add response validation hook
  fastify.addHook('onSend', (request: FastifyRequest, reply: FastifyReply, payload: unknown) => {
    if (!config.enabled) return payload;

    const operationId = extractOperationId(request) ?? `${request.method}_${request.url}`;

    const span = tracer.startSpan(`fastify_validate_response_${operationId}`);

    try {
      span.setAttributes({
        'http.method': request.method,
        'http.url': request.url,
        'http.status_code': reply.statusCode,
        'conformance.operation_id': operationId,
      });

      // Response validation would be handled by Fastify's built-in validation
      // This hook is mainly for telemetry

      span.setStatus({ code: SpanStatusCode.OK });

    } catch (error) {
      span.recordException(error as Error);
      span.setStatus({ code: SpanStatusCode.ERROR });
      
      if (config.logErrors) {
        console.error('Fastify response validation error:', error);
      }
    } finally {
      span.end();
    }

    return payload;
  });
}

/**
 * OpenAPI Integration Helper
 */
export class OpenAPIConformanceIntegration {
  private middleware: ExpressConformanceMiddleware;

  constructor(config: Partial<MiddlewareConfig> = {}) {
    this.middleware = new ExpressConformanceMiddleware(config);
  }

  /**
   * Generate middleware from OpenAPI operation
   */
  generateMiddleware(
    operation: {
      operationId: string;
      requestBody?: { schema: z.ZodSchema<unknown> };
      parameters?: Array<{ schema: z.ZodSchema<unknown>; in: 'query' | 'path' }>;
      responses?: Record<string, { schema: z.ZodSchema<unknown> }>;
    }
  ): ExpressMiddleware[] {
    const middlewares: ExpressMiddleware[] = [];

    // Request body validation
    if (operation.requestBody) {
      middlewares.push(
        this.middleware.validateRequestBody(operation.requestBody.schema, operation.operationId)
      );
    }

    // Parameter validation
    if (operation.parameters) {
      const queryParams = operation.parameters.filter(p => p.in === 'query');
      const pathParams = operation.parameters.filter(p => p.in === 'path');

      if (queryParams.length > 0) {
        // Combine query parameter schemas
        const queryShape = queryParams.reduce<ZodRawShape>((acc, param, index) => {
          acc[`param_${index}`] = param.schema;
          return acc;
        }, {});
        const querySchema = z.object(queryShape);
        middlewares.push(
          this.middleware.validateQueryParams(querySchema, operation.operationId)
        );
      }

      if (pathParams.length > 0) {
        // Combine path parameter schemas
        const pathShape = pathParams.reduce<ZodRawShape>((acc, param, index) => {
          acc[`param_${index}`] = param.schema;
          return acc;
        }, {});
        const pathSchema = z.object(pathShape);
        middlewares.push(
          this.middleware.validatePathParams(pathSchema, operation.operationId)
        );
      }
    }

    // Response validation (for 200 status)
    if (operation.responses?.['200']) {
      middlewares.push(
        this.middleware.validateResponse(operation.responses['200'].schema, operation.operationId)
      );
    }

    return middlewares;
  }
}

/**
 * Utility function to convert Zod schema to JSON Schema (simplified)
 */
function zodToJsonSchema(schema: ZodTypeAny): Record<string, unknown> {
  // This is a simplified implementation
  // In a real application, use a library like zod-to-json-schema
  if (schema instanceof z.ZodString) {
    return { type: 'string' };
  } else if (schema instanceof z.ZodNumber) {
    return { type: 'number' };
  } else if (schema instanceof z.ZodBoolean) {
    return { type: 'boolean' };
  } else if (schema instanceof z.ZodObject) {
    const properties: Record<string, unknown> = {};
    const shape = schema.shape as ZodRawShape;

    for (const key of Object.keys(shape)) {
      const rawValue = shape[key];
      if (!rawValue) {
        continue;
      }
      const value = rawValue as ZodTypeAny;
      properties[key] = zodToJsonSchema(value);
    }

    return {
      type: 'object',
      properties,
      required: Object.keys(shape),
    };
  }
  
  return { type: 'object' }; // Fallback
}

/**
 * Global middleware registry
 */
export class MiddlewareRegistry {
  private static instance: MiddlewareRegistry;
  private expressMiddleware: ExpressConformanceMiddleware;
  private registeredRoutes: Map<string, RegisteredRoute> = new Map();

  constructor(config: Partial<MiddlewareConfig> = {}) {
    this.expressMiddleware = new ExpressConformanceMiddleware(config);
  }

  static getInstance(config?: Partial<MiddlewareConfig>): MiddlewareRegistry {
    if (!MiddlewareRegistry.instance) {
      MiddlewareRegistry.instance = new MiddlewareRegistry(config);
    }
    return MiddlewareRegistry.instance;
  }

  /**
   * Register a route with validation
   */
  registerRoute(
    path: string,
    method: string,
    operationId: string,
    schemas: {
      request?: z.ZodSchema<unknown>;
      response?: z.ZodSchema<unknown>;
      query?: z.ZodSchema<unknown>;
      params?: z.ZodSchema<unknown>;
    }
  ): ExpressMiddleware[] {
    const middlewares: ExpressMiddleware[] = [];

    if (schemas.request) {
      middlewares.push(
        this.expressMiddleware.validateRequestBody(schemas.request, operationId)
      );
    }

    if (schemas.query) {
      middlewares.push(
        this.expressMiddleware.validateQueryParams(schemas.query, operationId)
      );
    }

    if (schemas.params) {
      middlewares.push(
        this.expressMiddleware.validatePathParams(schemas.params, operationId)
      );
    }

    if (schemas.response) {
      middlewares.push(
        this.expressMiddleware.validateResponse(schemas.response, operationId)
      );
    }

    const routeKey = `${method.toUpperCase()}:${path}`;
    this.registeredRoutes.set(routeKey, {
      operationId,
      middlewares,
      schemas,
    });

    return middlewares;
  }

  /**
   * Get middleware for a route
   */
  getMiddleware(path: string, method: string): ExpressMiddleware[] {
    const routeKey = `${method.toUpperCase()}:${path}`;
    const route = this.registeredRoutes.get(routeKey);
    return route ? route.middlewares : [];
  }

  /**
   * List all registered routes
   */
  listRoutes(): Array<{ path: string; method: string; operationId: string }> {
    return Array.from(this.registeredRoutes.entries()).map(([key, value]) => {
      const idx = key.indexOf(':');
      const method = idx >= 0 ? key.slice(0, idx) : key;
      const path = idx >= 0 ? key.slice(idx + 1) : '';
      return {
        path: path || '',
        method: method || '',
        operationId: value.operationId || '',
      };
    });
  }
}
