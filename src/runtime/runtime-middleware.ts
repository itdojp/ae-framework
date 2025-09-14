/**
 * Runtime Conformance Middleware
 * 
 * Express and Fastify middleware for automatic runtime contract validation
 * with OpenTelemetry integration and failure artifact generation
 */

// Express types - using any for maximum compatibility with optional dependency
// This approach maintains backward compatibility while allowing the middleware
// to work when Express is not installed
type Request = any;  // Express.Request when available
type Response = any; // Express.Response when available  
type NextFunction = any; // Express.NextFunction when available
import type { FastifyRequest, FastifyReply, FastifyInstance } from 'fastify';
import { z } from 'zod';
import { ConformanceGuard, GuardFactory } from './conformance-guards.js';
import type { ConformanceResult } from './conformance-guards.js';
import { trace } from '@opentelemetry/api';

const tracer = trace.getTracer('ae-framework-runtime-middleware');

// Middleware configuration
export interface MiddlewareConfig {
  enabled: boolean;
  strictMode: boolean; // Fail requests on validation errors
  logErrors: boolean;
  generateArtifacts: boolean;
  includeRequestInfo: boolean;
  customErrorHandler?: (error: any, req: any, res: any) => void;
}

const defaultMiddlewareConfig: MiddlewareConfig = {
  enabled: true,
  strictMode: false,
  logErrors: true,
  generateArtifacts: true,
  includeRequestInfo: true,
};

// Validation context for middleware
interface ValidationContext {
  operationId: string;
  method: string;
  path: string;
  timestamp: string;
  requestId?: string;
  userId?: string;
  [key: string]: any;
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
    
    return async (req: Request, res: Response, next: NextFunction) => {
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
        req.body = result.data;
        span.setStatus({ code: 1 as any });
        next();

      } catch (error) {
        span.recordException(error as Error);
        span.setStatus({ code: 2 as any });
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
    
    return async (req: Request, res: Response, next: NextFunction) => {
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

        req.query = result.data as any;
        span.setStatus({ code: 1 as any });
        next();

      } catch (error) {
        span.recordException(error as Error);
        span.setStatus({ code: 2 as any });
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
    
    return async (req: Request, res: Response, next: NextFunction) => {
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

        req.params = result.data as any;
        span.setStatus({ code: 1 as any });
        next();

      } catch (error) {
        span.recordException(error as Error);
        span.setStatus({ code: 2 as any });
        this.handleMiddlewareError(error, req, res, next);
      } finally {
        span.end();
      }
    };
  }

  /**
   * Validate response data
   */
  validateResponse<T>(schema: z.ZodSchema<T>, operationId: string) {
    const guard = GuardFactory.apiResponse(schema, operationId);
    
    return (req: Request, res: Response, next: NextFunction) => {
      if (!this.config.enabled) {
        return next();
      }

      const originalSend = res.send;
      const originalJson = res.json;

      // Intercept res.send
      res.send = function(data: any) {
        return validateAndSend.call(this, data, originalSend);
      } as any;

      // Intercept res.json
      res.json = function(data: any) {
        return validateAndSend.call(this, data, originalJson);
      } as any;

      const validateAndSend = async function(this: Response, data: any, originalMethod: Function) {
        const span = tracer.startSpan(`validate_response_${operationId}`);
        
        try {
          const context = this.createValidationContext(req, operationId);
          const result = await guard.validateOutput(data, context);

          span.setAttributes({
            'http.method': req.method,
            'http.route': req.route?.path || req.path,
            'conformance.operation_id': operationId,
            'conformance.validation_result': result.success ? 'success' : 'failure',
            'http.status_code': res.statusCode,
          });

          if (!result.success && this.config.logErrors) {
            console.warn(`🚨 Response validation failed for ${operationId}:`, result.errors);
          }

          span.setStatus({ code: 1 as any });
          
          // Always send the original data (don't break responses)
          return await Promise.resolve(originalMethod.call(this, data));

        } catch (error) {
          span.recordException(error as Error);
          span.setStatus({ code: 2 as any });
          
          if (this.config.logErrors) {
            console.error(`Response validation error for ${operationId}:`, error);
          }
          
          // Still send the response
          return await Promise.resolve(originalMethod.call(this, data));
        } finally {
          span.end();
        }
      }.bind(this);

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
    return [
      requestSchema ? (
        target === 'body' ? this.validateRequestBody(requestSchema, operationId) :
        target === 'query' ? this.validateQueryParams(requestSchema, operationId) :
        this.validatePathParams(requestSchema, operationId)
      ) : undefined,
      responseSchema ? this.validateResponse(responseSchema, operationId) : undefined,
    ].filter(Boolean) as any[];
  }

  private createValidationContext(req: Request, operationId: string): ValidationContext {
    const context: ValidationContext = {
      operationId,
      method: req.method,
      path: req.path,
      timestamp: new Date().toISOString(),
    };

    if (this.config.includeRequestInfo) {
      context['requestId'] = req.headers['x-request-id'] as string;
      context['userId'] = (req as any).user?.id;
      context['userAgent'] = req.get('User-Agent');
      context['ip'] = req.ip;
    }

    return context;
  }

  private handleValidationError(
    result: ConformanceResult,
    req: Request,
    res: Response,
    next: NextFunction,
    target: string
  ): void {
    const error = {
      error: 'Validation Failed',
      message: `${target} validation failed`,
      details: result.errors,
      timestamp: result.metadata.timestamp,
      path: req.path,
      method: req.method,
    };

    if (this.config.customErrorHandler) {
      return this.config.customErrorHandler(error, req, res);
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
    error: any,
    req: Request,
    res: Response,
    next: NextFunction
  ): void {
    if (this.config.customErrorHandler) {
      return this.config.customErrorHandler(error, req, res);
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

/**
 * Fastify Plugin for Runtime Conformance
 */
export async function fastifyConformancePlugin(
  fastify: FastifyInstance,
  options: {
    config?: Partial<MiddlewareConfig>;
    schemas?: Record<string, z.ZodSchema<any>>;
  } = {}
) {
  const config = { ...defaultMiddlewareConfig, ...options.config };
  const { schemas = {} } = options;

  // Register schemas
  for (const [name, schema] of Object.entries(schemas)) {
    fastify.addSchema({
      $id: name,
      ...zodToJsonSchema(schema),
    });
  }

  // Add validation hook
  fastify.addHook('preHandler', async (request: FastifyRequest, reply: FastifyReply) => {
    if (!config.enabled) return;

    const operationId = ((request as any).routerMethod as any)?.operationId || 
                       `${request.method}_${request.url}`;

    const span = tracer.startSpan(`fastify_validate_${operationId}`);

    try {
      span.setAttributes({
        'http.method': request.method,
        'http.url': request.url,
        'conformance.operation_id': operationId,
      });

      // Validation would be handled by Fastify's built-in JSON schema validation
      // This hook is mainly for telemetry and artifact generation

      span.setStatus({ code: 1 as any });

    } catch (error) {
      span.recordException(error as Error);
      span.setStatus({ code: 2 as any });
      throw error;
    } finally {
      span.end();
    }
  });

  // Add response validation hook
  fastify.addHook('onSend', async (request: FastifyRequest, reply: FastifyReply, payload: any) => {
    if (!config.enabled) return payload;

    const operationId = ((request as any).routerMethod as any)?.operationId || 
                       `${request.method}_${request.url}`;

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

      span.setStatus({ code: 1 as any });

    } catch (error) {
      span.recordException(error as Error);
      span.setStatus({ code: 2 as any });
      
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
      requestBody?: { schema: z.ZodSchema<any> };
      parameters?: Array<{ schema: z.ZodSchema<any>; in: 'query' | 'path' }>;
      responses?: { [status: string]: { schema: z.ZodSchema<any> } };
    }
  ) {
    const middlewares: any[] = [];

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
        const querySchema = z.object(
          queryParams.reduce((acc, param, index) => {
            acc[`param_${index}`] = param.schema;
            return acc;
          }, {} as any)
        );
        middlewares.push(
          this.middleware.validateQueryParams(querySchema, operation.operationId)
        );
      }

      if (pathParams.length > 0) {
        // Combine path parameter schemas
        const pathSchema = z.object(
          pathParams.reduce((acc, param, index) => {
            acc[`param_${index}`] = param.schema;
            return acc;
          }, {} as any)
        );
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
function zodToJsonSchema(schema: z.ZodSchema<any>): any {
  // This is a simplified implementation
  // In a real application, use a library like zod-to-json-schema
  if (schema instanceof z.ZodString) {
    return { type: 'string' };
  } else if (schema instanceof z.ZodNumber) {
    return { type: 'number' };
  } else if (schema instanceof z.ZodBoolean) {
    return { type: 'boolean' };
  } else if (schema instanceof z.ZodObject) {
    const properties: any = {};
    const shape = (schema as any)._def.shape();
    
    for (const [key, value] of Object.entries(shape)) {
      properties[key] = zodToJsonSchema(value as z.ZodSchema<any>);
    }
    
    return {
      type: 'object',
      properties,
      required: Object.keys(properties),
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
  private registeredRoutes: Map<string, any> = new Map();

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
      request?: z.ZodSchema<any>;
      response?: z.ZodSchema<any>;
      query?: z.ZodSchema<any>;
      params?: z.ZodSchema<any>;
    }
  ): any[] {
    const middlewares = [];

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
  getMiddleware(path: string, method: string): any[] {
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
