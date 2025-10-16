/**
 * Runtime Conformance Guards
 * 
 * Zod-based runtime validation with OpenTelemetry integration
 * for detecting contract mismatches and specification drift
 */

import { z } from 'zod';
import { trace, metrics as otMetrics, SpanStatusCode } from '@opentelemetry/api';
import type { Attributes, Span } from '@opentelemetry/api';
import type { FailureLocation } from '../cegis/failure-artifact-schema.js';
import { FailureArtifactFactory } from '../cegis/failure-artifact-schema.js';

// Telemetry instances (safe for partially mocked @opentelemetry/api)
const tracer = trace.getTracer('ae-framework-runtime-conformance');

type MiddlewareRequest = {
  body: unknown;
  query: unknown;
  params: unknown;
  method: string;
  originalUrl: string;
  ip?: string;
  get: (name: string) => string | undefined;
};

type MiddlewareResponse = {
  status: (code: number) => { json: (payload: unknown) => unknown };
};

type MiddlewareNext = () => void;

type CounterLike = { add: (value: number, attrs?: Attributes) => void };
type HistogramLike = { record: (value: number, attrs?: Attributes) => void };
type MeterLike = {
  createCounter: (name: string, opts?: Record<string, unknown>) => CounterLike;
  createHistogram: (name: string, opts?: Record<string, unknown>) => HistogramLike;
};

function getSafeMeter(): MeterLike {
  try {
    if (typeof otMetrics.getMeter === 'function') {
      return otMetrics.getMeter('ae-framework-runtime-conformance');
    }
  } catch {
    // Metrics API may be partially mocked in tests; fall back to no-op meter.
  }
  // No-op fallbacks
  return {
    createCounter: () => ({ add: () => {} }),
    createHistogram: () => ({ record: () => {} }),
  };
}

const meter = getSafeMeter();

const mergeContext = (
  base?: ConformanceContext,
  incoming?: ConformanceContext
): ConformanceContext | undefined => {
  if (!base && !incoming) {
    return undefined;
  }
  return {
    ...(base ?? {}),
    ...(incoming ?? {}),
  };
};

const getOwnerName = (target: object): string => {
  if (typeof target === 'function' && target.name) {
    return target.name;
  }
  const constructorRef = (target as { constructor?: { name?: string } }).constructor;
  if (constructorRef && typeof constructorRef.name === 'string' && constructorRef.name.length > 0) {
    return constructorRef.name;
  }
  return 'Anonymous';
};

// Metrics
const conformanceCounter = meter.createCounter('conformance_checks_total', {
  description: 'Total number of conformance checks performed',
});

const conformanceViolationCounter = meter.createCounter('conformance_violations_total', {
  description: 'Total number of conformance violations detected',
});

const conformanceLatencyHistogram = meter.createHistogram('conformance_check_duration_ms', {
  description: 'Duration of conformance checks in milliseconds',
});

// Conformance check result
export interface ConformanceResult<T = unknown> {
  success: boolean;
  data?: T;
  errors: string[];
  warnings: string[];
  metadata: {
    schemaName?: string;
    duration: number;
    timestamp: string;
    context?: ConformanceContext;
  };
}

// Guard configuration
export interface ConformanceContext extends Record<string, unknown> {
  source?: string;
  schema?: string;
  schemaName?: string;
  name?: string;
  operation?: string;
  type?: string;
  eventType?: string;
  location?: FailureLocation;
}

export interface GuardConfig {
  enabled: boolean;
  failOnViolation: boolean;
  logViolations: boolean;
  generateArtifacts: boolean;
  telemetryEnabled: boolean;
  context?: ConformanceContext;
}

// Default guard configuration
const defaultConfig: GuardConfig = {
  enabled: true,
  failOnViolation: false,
  logViolations: true,
  generateArtifacts: true,
  telemetryEnabled: true,
};

/**
 * Runtime Conformance Guard
 * 
 * Validates data against Zod schemas with telemetry and error handling
 */
export class ConformanceGuard<T> {
  private schema: z.ZodSchema<T>;
  private schemaName: string;
  private config: GuardConfig;

  constructor(
    schema: z.ZodSchema<T>,
    schemaName: string,
    config: Partial<GuardConfig> = {}
  ) {
    this.schema = schema;
    this.schemaName = schemaName;
    this.config = { ...defaultConfig, ...config };
  }

  /**
   * Validate input data against schema
   */
  validateInput(data: unknown, context?: ConformanceContext): Promise<ConformanceResult<T>> {
    return Promise.resolve(this.validate(data, 'input', context));
  }

  /**
   * Validate output data against schema
   */
  validateOutput(data: unknown, context?: ConformanceContext): Promise<ConformanceResult<T>> {
    return Promise.resolve(this.validate(data, 'output', context));
  }

  /**
   * Core validation logic with telemetry
   */
  private validate(
    data: unknown,
    direction: 'input' | 'output',
    context?: ConformanceContext
  ): ConformanceResult<T> {
    const mergedContext = mergeContext(this.config.context, context);

    if (!this.config.enabled) {
      return {
        success: true,
        data: data as T,
        errors: [],
        warnings: ['Conformance checking is disabled'],
        metadata: {
          schemaName: this.schemaName,
          duration: 0,
          timestamp: new Date().toISOString(),
          ...(mergedContext ? { context: mergedContext } : {}),
        },
      };
    }

    const startTime = Date.now();
    let span: Span | undefined;
    
    if (this.config.telemetryEnabled) {
      span = tracer.startSpan(`conformance_check_${direction}`, {
        attributes: {
          'conformance.schema_name': this.schemaName,
          'conformance.direction': direction,
          'conformance.data_type': typeof data,
        },
      });
    }

    try {
      // Increment check counter
      if (this.config.telemetryEnabled) {
        conformanceCounter.add(1, {
          schema_name: this.schemaName,
          direction,
          result: 'attempted',
        });
      }

      // Perform validation
      const result = this.schema.safeParse(data);
      const duration = Date.now() - startTime;

      if (this.config.telemetryEnabled) {
        conformanceLatencyHistogram.record(duration, {
          schema_name: this.schemaName,
          direction,
        });
      }

      if (result.success) {
        // Validation passed
        if (span) {
          span.setStatus({ code: SpanStatusCode.OK });
          span.setAttributes({
            'conformance.result': 'success',
            'conformance.duration_ms': duration,
          });
        }

        if (this.config.telemetryEnabled) {
          conformanceCounter.add(1, {
            schema_name: this.schemaName,
            direction,
            result: 'success',
          });
        }

        return {
          success: true,
          data: result.data,
          errors: [],
          warnings: [],
          metadata: {
            schemaName: this.schemaName,
            duration,
            timestamp: new Date().toISOString(),
            ...(mergedContext ? { context: mergedContext } : {}),
          },
        };
      } else {
        // Validation failed
        const errors = result.error.errors.map(err => 
          `${err.path.join('.')}: ${err.message}`
        );

        if (span) {
          span.setStatus({
            code: SpanStatusCode.ERROR,
            message: `Conformance violation: ${errors.join(', ')}`,
          });
          span.setAttributes({
            'conformance.result': 'violation',
            'conformance.error_count': errors.length,
            'conformance.duration_ms': duration,
          });
        }

        // Record violation metrics
        if (this.config.telemetryEnabled) {
          conformanceViolationCounter.add(1, {
            schema_name: this.schemaName,
            direction,
            severity: 'error',
          });

          conformanceCounter.add(1, {
            schema_name: this.schemaName,
            direction,
            result: 'violation',
          });
        }

        // Log violation if configured
        if (this.config.logViolations) {
          console.warn(`🚨 Conformance violation in ${this.schemaName} (${direction}):`, {
            errors,
            data: this.sanitizeForLogging(data),
            duration,
          });
        }

        // Generate failure artifact if configured
        if (this.config.generateArtifacts) {
          this.generateFailureArtifact(errors, data, direction, mergedContext);
        }

        // Throw error if configured to fail on violation
        if (this.config.failOnViolation) {
          throw new ConformanceViolationError(
            `Conformance violation in ${this.schemaName} (${direction}): ${errors.join(', ')}`,
            this.schemaName,
            direction,
            errors,
            data
          );
        }

        return {
          success: false,
          errors,
          warnings: [],
          metadata: {
            schemaName: this.schemaName,
            duration,
            timestamp: new Date().toISOString(),
            ...(mergedContext ? { context: mergedContext } : {}),
          },
        };
      }
    } catch (error) {
      if (span) {
        const normalizedError = error instanceof Error ? error : new Error(String(error));
        span.recordException(normalizedError);
        span.setStatus({
          code: SpanStatusCode.ERROR,
          message: `Conformance check failed: ${normalizedError.message}`,
        });
      }

      throw error;
    } finally {
      if (span) {
        span.end();
      }
    }
  }

  /**
   * Generate failure artifact for conformance violations
   */
  private generateFailureArtifact(
    errors: string[],
    data: unknown,
    direction: 'input' | 'output',
    context?: ConformanceContext
  ): void {
    try {
      const artifact = FailureArtifactFactory.fromContractViolation(
        `${this.schemaName} (${direction})`,
        'Schema validation',
        data,
        context?.location
      );

      artifact.evidence.logs.push(
        ...errors.map((error) => `Validation error: ${error}`)
      );

      if (context) {
        let serializedContext: string | undefined;
        try {
          serializedContext = JSON.stringify(context);
        } catch {
          serializedContext = undefined;
        }

        artifact.evidence.environmentInfo = {
          ...artifact.evidence.environmentInfo,
          direction,
          schema: this.schemaName,
          ...(serializedContext ? { context: serializedContext } : {}),
        };
      }

      // In a real implementation, this would store the artifact
      console.debug('📝 Generated failure artifact:', artifact.id);
    } catch (error) {
      console.error('Failed to generate failure artifact:', error);
    }
  }

  /**
   * Sanitize data for logging (remove sensitive information)
   */
  private sanitizeForLogging(data: unknown): unknown {
    if (data === null || typeof data !== 'object') {
      return data;
    }

    const sensitiveFragments = ['password', 'token', 'secret', 'key', 'authorization'];

    let clone: unknown;
    try {
      clone = JSON.parse(JSON.stringify(data));
    } catch {
      return '[Unserializable payload]';
    }

    const sanitizeRecursive = (value: unknown): unknown => {
      if (Array.isArray(value)) {
        return value.map(sanitizeRecursive);
      }

      if (value && typeof value === 'object') {
        const result: Record<string, unknown> = {};
        for (const [key, nestedValue] of Object.entries(value as Record<string, unknown>)) {
          const lowerKey = key.toLowerCase();
          if (sensitiveFragments.some((fragment) => lowerKey.includes(fragment))) {
            result[key] = '[REDACTED]';
          } else {
            result[key] = sanitizeRecursive(nestedValue);
          }
        }
        return result;
      }

      return value;
    };

    return sanitizeRecursive(clone);
  }

  /**
   * Update guard configuration
   */
  updateConfig(newConfig: Partial<GuardConfig>): void {
    this.config = { ...this.config, ...newConfig };
  }

  /**
   * Get current configuration
   */
  getConfig(): GuardConfig {
    return { ...this.config };
  }

  getSchemaName(): string {
    return this.schemaName;
  }
}

/**
 * Conformance Violation Error
 */
export class ConformanceViolationError extends Error {
  constructor(
    message: string,
    public schemaName: string,
    public direction: 'input' | 'output',
    public validationErrors: string[],
    public data: unknown
  ) {
    super(message);
    this.name = 'ConformanceViolationError';
  }
}

/**
 * Factory for creating common guards
 */
export class GuardFactory {
  /**
   * Create API request guard
   */
  static apiRequest<T>(schema: z.ZodSchema<T>, operationId: string): ConformanceGuard<T> {
    return new ConformanceGuard(schema, `api.request.${operationId}`, {
      failOnViolation: true,
      logViolations: true,
      generateArtifacts: true,
      context: {
        type: 'api_request',
        operation: operationId,
        schemaName: `api.request.${operationId}`,
      },
    });
  }

  /**
   * Create API response guard
   */
  static apiResponse<T>(schema: z.ZodSchema<T>, operationId: string): ConformanceGuard<T> {
    return new ConformanceGuard(schema, `api.response.${operationId}`, {
      failOnViolation: false, // Don't fail response validation in production
      logViolations: true,
      generateArtifacts: true,
      context: {
        type: 'api_response',
        operation: operationId,
        schemaName: `api.response.${operationId}`,
      },
    });
  }

  /**
   * Create database entity guard
   */
  static databaseEntity<T>(schema: z.ZodSchema<T>, entityName: string): ConformanceGuard<T> {
    return new ConformanceGuard(schema, `db.entity.${entityName}`, {
      failOnViolation: true,
      logViolations: true,
      generateArtifacts: true,
      context: {
        type: 'database_entity',
        entity: entityName,
        schemaName: `db.entity.${entityName}`,
      },
    });
  }

  /**
   * Create configuration guard
   */
  static configuration<T>(schema: z.ZodSchema<T>, configName: string): ConformanceGuard<T> {
    return new ConformanceGuard(schema, `config.${configName}`, {
      failOnViolation: true,
      logViolations: true,
      generateArtifacts: false, // Config errors don't need artifacts
      context: {
        type: 'configuration',
        config: configName,
        schemaName: `config.${configName}`,
      },
    });
  }

  /**
   * Create event guard
   */
  static event<T>(schema: z.ZodSchema<T>, eventType: string): ConformanceGuard<T> {
    return new ConformanceGuard(schema, `event.${eventType}`, {
      failOnViolation: false, // Events shouldn't break processing
      logViolations: true,
      generateArtifacts: true,
      context: {
        type: 'event',
        eventType,
        schemaName: `event.${eventType}`,
      },
    });
  }
}

/**
 * Decorator for automatic method validation
 */
export function ValidateInput<T>(guard: ConformanceGuard<T>) {
  return function <
    TTarget extends object,
    TArgs extends unknown[],
    TResult
  >(
    target: TTarget,
    propertyKey: string,
    descriptor?: TypedPropertyDescriptor<(...args: TArgs) => TResult>
  ): TypedPropertyDescriptor<(...args: TArgs) => TResult> | void {
    const baseDescriptor =
      descriptor ?? Object.getOwnPropertyDescriptor(target, propertyKey);

    const originalValue: unknown = baseDescriptor?.value;
    if (typeof originalValue !== 'function') {
      return baseDescriptor;
    }
    const originalMethod = originalValue as (...args: TArgs) => TResult;

    const ownerName = getOwnerName(target);

    const wrapped = async function (this: unknown, input: unknown, ...args: TArgs): Promise<TResult> {
      const result = await guard.validateInput(input, {
        method: `${ownerName}.${propertyKey}`,
        timestamp: new Date().toISOString(),
      });

      if (!result.success && guard.getConfig().failOnViolation) {
        throw new ConformanceViolationError(
          `Input validation failed for ${propertyKey}`,
          guard.getSchemaName(),
          'input',
          result.errors,
          input
        );
      }

      const callArgs: unknown[] = [result.data ?? input, ...args];
      return Reflect.apply(originalMethod, this, callArgs) as TResult;
    };

    const updatedDescriptor: PropertyDescriptor = {
      value: wrapped,
      configurable: baseDescriptor?.configurable ?? true,
      enumerable: baseDescriptor?.enumerable ?? false,
      writable: baseDescriptor?.writable ?? true,
    };

    try {
      Object.defineProperty(target, propertyKey, updatedDescriptor);
    } catch {
      // best-effort
    }

    return undefined;
  };
}

/**
 * Decorator for automatic output validation
 */
export function ValidateOutput<T>(guard: ConformanceGuard<T>) {
  return function <
    TTarget extends object,
    TArgs extends unknown[],
    TResult
  >(
    target: TTarget,
    propertyKey: string,
    descriptor?: TypedPropertyDescriptor<(...args: TArgs) => TResult>
  ): TypedPropertyDescriptor<(...args: TArgs) => TResult> | void {
    const baseDescriptor =
      descriptor ?? Object.getOwnPropertyDescriptor(target, propertyKey);

    const originalValue: unknown = baseDescriptor?.value;
    if (typeof originalValue !== 'function') {
      return baseDescriptor;
    }
    const originalMethod = originalValue as (...args: TArgs) => TResult;

    const ownerName = getOwnerName(target);

    const wrapped = async function (this: unknown, ...args: TArgs): Promise<TResult> {
      const result = await Reflect.apply(originalMethod, this, args) as TResult;

      const validationResult = await guard.validateOutput(result, {
        method: `${ownerName}.${propertyKey}`,
        timestamp: new Date().toISOString(),
      });

      if (!validationResult.success && guard.getConfig().failOnViolation) {
        throw new ConformanceViolationError(
          `Output validation failed for ${propertyKey}`,
          guard.getSchemaName(),
          'output',
          validationResult.errors,
          result
        );
      }

      return result;
    };

    const updatedDescriptor: PropertyDescriptor = {
      value: wrapped,
      configurable: baseDescriptor?.configurable ?? true,
      enumerable: baseDescriptor?.enumerable ?? false,
      writable: baseDescriptor?.writable ?? true,
    };

    try {
      Object.defineProperty(target, propertyKey, updatedDescriptor);
    } catch {
      // best-effort
    }

    return undefined;
  };
}

/**
 * Middleware factory for Express.js integration
 */
export function createExpressMiddleware<T>(
  guard: ConformanceGuard<T>,
  target: 'body' | 'query' | 'params' = 'body'
) {
  return async (req: MiddlewareRequest, res: MiddlewareResponse, next: MiddlewareNext) => {
    try {
      const data =
        target === 'body'
          ? req.body
          : target === 'query'
            ? req.query
            : req.params;

      const result = await guard.validateInput(data, {
        method: req.method,
        url: req.originalUrl,
        userAgent: req.get('User-Agent'),
        ip: req.ip,
      });

      if (!result.success) {
        if (guard.getConfig().failOnViolation) {
          res.status(400).json({
            error: 'Validation failed',
            details: result.errors,
            timestamp: result.metadata.timestamp,
          });
          return;
        } else {
          // Log but continue
          console.warn('Validation failed but continuing:', result.errors);
        }
      }

      // Attach validated data
      if (typeof result.data !== 'undefined') {
        if (target === 'body') {
          req.body = result.data;
        } else if (target === 'query') {
          req.query = result.data;
        } else {
          req.params = result.data;
        }
      }

      next();
    } catch (error) {
      console.error('Conformance middleware error:', error);
      if (guard.getConfig().failOnViolation) {
        res.status(500).json({
          error: 'Internal validation error',
          timestamp: new Date().toISOString(),
        });
        return;
      }
      next();
    }
  };
}

/**
 * Global conformance registry for schema management
 */
export class ConformanceRegistry {
  private static instance: ConformanceRegistry;
  private guards: Map<string, ConformanceGuard<unknown>> = new Map();
  private schemas: Map<string, z.ZodSchema<unknown>> = new Map();

  static getInstance(): ConformanceRegistry {
    if (!ConformanceRegistry.instance) {
      ConformanceRegistry.instance = new ConformanceRegistry();
    }
    return ConformanceRegistry.instance;
  }

  /**
   * Register a schema with the registry
   */
  registerSchema<T>(name: string, schema: z.ZodSchema<T>): void {
    this.schemas.set(name, schema as z.ZodSchema<unknown>);
  }

  /**
   * Register a guard with the registry
   */
  registerGuard<T>(name: string, guard: ConformanceGuard<T>): void {
    this.guards.set(name, guard as ConformanceGuard<unknown>);
  }

  /**
   * Get a guard by name
   */
  getGuard<T>(name: string): ConformanceGuard<T> | undefined {
    return this.guards.get(name) as ConformanceGuard<T> | undefined;
  }

  /**
   * Get a schema by name
   */
  getSchema<T>(name: string): z.ZodSchema<T> | undefined {
    return this.schemas.get(name) as z.ZodSchema<T> | undefined;
  }

  /**
   * Create a guard from a registered schema
   */
  createGuard<T>(schemaName: string, guardName?: string, config?: Partial<GuardConfig>): ConformanceGuard<T> | null {
    const schema = this.schemas.get(schemaName) as z.ZodSchema<T> | undefined;
    if (!schema) {
      console.warn(`Schema '${schemaName}' not found in registry`);
      return null;
    }

    // デフォルトのcontextを付与（テスト互換用）
    const baseContext: ConformanceContext = {
      source: 'registry',
      schema: schemaName,
      schemaName,
      name: guardName || schemaName,
    };
    const mergedContextValue = mergeContext(baseContext, config?.context);
    const mergedConfig: Partial<GuardConfig> = {
      ...(config || {}),
      ...(mergedContextValue ? { context: mergedContextValue } : {}),
    };
    const guard = new ConformanceGuard<T>(schema, guardName || schemaName, mergedConfig);
    if (guardName) {
      this.registerGuard(guardName, guard);
    }

    return guard;
  }

  /**
   * List all registered schemas
   */
  listSchemas(): string[] {
    return Array.from(this.schemas.keys());
  }

  /**
   * List all registered guards
   */
  listGuards(): string[] {
    return Array.from(this.guards.keys());
  }

  /**
   * Clear all registrations
   */
  clear(): void {
    this.guards.clear();
    this.schemas.clear();
  }
}
