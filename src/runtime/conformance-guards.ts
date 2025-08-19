/**
 * Runtime Conformance Guards
 * 
 * Zod-based runtime validation with OpenTelemetry integration
 * for detecting contract mismatches and specification drift
 */

import { z } from 'zod';
import { trace, metrics, SpanStatusCode, SpanKind } from '@opentelemetry/api';
import { FailureArtifactFactory } from '../cegis/failure-artifact-schema.js';

// Telemetry instances
const tracer = trace.getTracer('ae-framework-runtime-conformance');
const meter = metrics.getMeter('ae-framework-runtime-conformance');

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
export interface ConformanceResult<T = any> {
  success: boolean;
  data?: T;
  errors: string[];
  warnings: string[];
  metadata: {
    schemaName?: string;
    duration: number;
    timestamp: string;
    context?: Record<string, any>;
  };
}

// Guard configuration
export interface GuardConfig {
  enabled: boolean;
  failOnViolation: boolean;
  logViolations: boolean;
  generateArtifacts: boolean;
  telemetryEnabled: boolean;
  context?: Record<string, any>;
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
  async validateInput(data: unknown, context?: Record<string, any>): Promise<ConformanceResult<T>> {
    return this.validate(data, 'input', context);
  }

  /**
   * Validate output data against schema
   */
  async validateOutput(data: unknown, context?: Record<string, any>): Promise<ConformanceResult<T>> {
    return this.validate(data, 'output', context);
  }

  /**
   * Core validation logic with telemetry
   */
  private async validate(
    data: unknown, 
    direction: 'input' | 'output',
    context?: Record<string, any>
  ): Promise<ConformanceResult<T>> {
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
          context,
        },
      };
    }

    const startTime = Date.now();
    let span;
    
    if (this.config.telemetryEnabled) {
      span = tracer.startSpan(`conformance_check_${direction}`, {
        kind: SpanKind.INTERNAL,
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
            context: { ...this.config.context, ...context },
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
          await this.generateFailureArtifact(errors, data, direction, context);
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
            context: { ...this.config.context, ...context },
          },
        };
      }
    } catch (error) {
      const duration = Date.now() - startTime;
      
      if (span) {
        span.recordException(error as Error);
        span.setStatus({
          code: SpanStatusCode.ERROR,
          message: `Conformance check failed: ${error}`,
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
  private async generateFailureArtifact(
    errors: string[],
    data: unknown,
    direction: 'input' | 'output',
    context?: Record<string, any>
  ): Promise<void> {
    try {
      const artifact = FailureArtifactFactory.fromContractViolation(
        `${this.schemaName} (${direction})`,
        'Schema validation',
        data,
        context?.location
      );

      // Add additional context
      artifact.evidence.logs.push(
        ...errors.map(error => `Validation error: ${error}`)
      );

      if (context) {
        artifact.evidence.environmentInfo = {
          ...artifact.evidence.environmentInfo,
          direction,
          schema: this.schemaName,
          context: JSON.stringify(context),
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
  private sanitizeForLogging(data: unknown): any {
    if (typeof data !== 'object' || data === null) {
      return data;
    }

    const sensitiveKeys = ['password', 'token', 'secret', 'key', 'authorization'];
    const sanitized = JSON.parse(JSON.stringify(data));

    const sanitizeObject = (obj: any): any => {
      for (const key in obj) {
        if (typeof obj[key] === 'object' && obj[key] !== null) {
          sanitizeObject(obj[key]);
        } else if (sensitiveKeys.some(sk => key.toLowerCase().includes(sk))) {
          obj[key] = '[REDACTED]';
        }
      }
      return obj;
    };

    return sanitizeObject(sanitized);
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
      context: { type: 'api_request', operation: operationId },
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
      context: { type: 'api_response', operation: operationId },
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
      context: { type: 'database_entity', entity: entityName },
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
      context: { type: 'configuration', config: configName },
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
      context: { type: 'event', eventType },
    });
  }
}

/**
 * Decorator for automatic method validation
 */
export function ValidateInput<T>(guard: ConformanceGuard<T>) {
  return function (target: any, propertyKey: string, descriptor: PropertyDescriptor) {
    const originalMethod = descriptor.value;

    descriptor.value = async function (input: unknown, ...args: any[]) {
      const result = await guard.validateInput(input, {
        method: `${target.constructor.name}.${propertyKey}`,
        timestamp: new Date().toISOString(),
      });

      if (!result.success && guard.getConfig().failOnViolation) {
        throw new ConformanceViolationError(
          `Input validation failed for ${propertyKey}`,
          guard.getConfig().context?.schema_name || 'unknown',
          'input',
          result.errors,
          input
        );
      }

      return originalMethod.call(this, result.data || input, ...args);
    };

    return descriptor;
  };
}

/**
 * Decorator for automatic output validation
 */
export function ValidateOutput<T>(guard: ConformanceGuard<T>) {
  return function (target: any, propertyKey: string, descriptor: PropertyDescriptor) {
    const originalMethod = descriptor.value;

    descriptor.value = async function (...args: any[]) {
      const result = await originalMethod.apply(this, args);
      
      const validationResult = await guard.validateOutput(result, {
        method: `${target.constructor.name}.${propertyKey}`,
        timestamp: new Date().toISOString(),
      });

      if (!validationResult.success && guard.getConfig().failOnViolation) {
        throw new ConformanceViolationError(
          `Output validation failed for ${propertyKey}`,
          guard.getConfig().context?.schema_name || 'unknown',
          'output',
          validationResult.errors,
          result
        );
      }

      return result;
    };

    return descriptor;
  };
}

/**
 * Middleware factory for Express.js integration
 */
export function createExpressMiddleware<T>(
  guard: ConformanceGuard<T>,
  target: 'body' | 'query' | 'params' = 'body'
) {
  return async (req: any, res: any, next: any) => {
    try {
      const data = target === 'body' ? req.body : 
                   target === 'query' ? req.query : 
                   req.params;

      const result = await guard.validateInput(data, {
        method: req.method,
        url: req.originalUrl,
        userAgent: req.get('User-Agent'),
        ip: req.ip,
      });

      if (!result.success) {
        if (guard.getConfig().failOnViolation) {
          return res.status(400).json({
            error: 'Validation failed',
            details: result.errors,
            timestamp: result.metadata.timestamp,
          });
        } else {
          // Log but continue
          console.warn('Validation failed but continuing:', result.errors);
        }
      }

      // Attach validated data
      if (target === 'body') req.body = result.data || req.body;
      if (target === 'query') req.query = result.data || req.query;
      if (target === 'params') req.params = result.data || req.params;

      next();
    } catch (error) {
      console.error('Conformance middleware error:', error);
      if (guard.getConfig().failOnViolation) {
        return res.status(500).json({
          error: 'Internal validation error',
          timestamp: new Date().toISOString(),
        });
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
  private guards: Map<string, ConformanceGuard<any>> = new Map();
  private schemas: Map<string, z.ZodSchema<any>> = new Map();

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
    this.schemas.set(name, schema);
  }

  /**
   * Register a guard with the registry
   */
  registerGuard<T>(name: string, guard: ConformanceGuard<T>): void {
    this.guards.set(name, guard);
  }

  /**
   * Get a guard by name
   */
  getGuard<T>(name: string): ConformanceGuard<T> | undefined {
    return this.guards.get(name);
  }

  /**
   * Get a schema by name
   */
  getSchema<T>(name: string): z.ZodSchema<T> | undefined {
    return this.schemas.get(name);
  }

  /**
   * Create a guard from a registered schema
   */
  createGuard<T>(schemaName: string, guardName?: string, config?: Partial<GuardConfig>): ConformanceGuard<T> | null {
    const schema = this.schemas.get(schemaName);
    if (!schema) {
      console.warn(`Schema '${schemaName}' not found in registry`);
      return null;
    }

    const guard = new ConformanceGuard(schema, guardName || schemaName, config);
    
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