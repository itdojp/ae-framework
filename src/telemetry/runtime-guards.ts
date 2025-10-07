/**
 * Runtime Guards with OpenTelemetry Integration
 * Implements comprehensive request/response validation with telemetry tracking
 */

import { z } from 'zod';
import type { FastifyRequest, FastifyReply } from 'fastify';
import { enhancedTelemetry, TELEMETRY_ATTRIBUTES } from './enhanced-telemetry.js';
import { trace, context } from '@opentelemetry/api';

const HOUR_IN_MS = 60 * 60 * 1000;

// Contract violation types
export enum ViolationType {
  SCHEMA_VALIDATION = 'schema_validation',
  RATE_LIMIT = 'rate_limit',
  AUTHORIZATION = 'authorization',
  BUSINESS_RULE = 'business_rule',
  DATA_INTEGRITY = 'data_integrity',
  TIMEOUT = 'timeout',
}

// Severity levels for contract violations
export enum ViolationSeverity {
  LOW = 'low',
  MEDIUM = 'medium',
  HIGH = 'high',
  CRITICAL = 'critical',
}

export interface ContractViolation {
  id: string;
  type: ViolationType;
  severity: ViolationSeverity;
  message: string;
  timestamp: Date;
  requestId?: string;
  endpoint?: string;
  details?: Record<string, any>;
}

export interface HourlyViolationBucket {
  hour: string;
  count: number;
}

export interface ViolationStats {
  total: number;
  byType: Record<ViolationType, number>;
  bySeverity: Record<ViolationSeverity, number>;
  byEndpoint: Record<string, number>;
  last24Hours: {
    total: number;
    byType: Record<ViolationType, number>;
    bySeverity: Record<ViolationSeverity, number>;
    hourlyBuckets: HourlyViolationBucket[];
  };
  recent: Array<{
    id: string;
    type: ViolationType;
    severity: ViolationSeverity;
    endpoint: string | null;
    timestamp: string;
  }>;
}

export interface ValidationResult {
  valid: boolean;
  data?: any;
  violations: ContractViolation[];
}

export class RuntimeGuard {
  private tracer = trace.getTracer('ae-framework-runtime-guards');
  private violations: ContractViolation[] = [];

  /**
   * Validate request payload against Zod schema
   */
  public validateRequest<T>(
    schema: z.ZodSchema<T>,
    data: unknown,
    context: {
      requestId?: string;
      endpoint?: string;
      operation?: string;
    } = {}
  ): ValidationResult {
    const span = this.tracer.startSpan('runtime_guard.validate_request', {
      attributes: {
        [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'runtime-guard',
        [TELEMETRY_ATTRIBUTES.SERVICE_OPERATION]: context.operation || 'validate_request',
        [TELEMETRY_ATTRIBUTES.REQUEST_ID]: context.requestId || 'unknown',
        endpoint: context.endpoint || 'unknown',
      },
    });

    try {
      const timer = enhancedTelemetry.createTimer('runtime_guard.validation.duration');
      const result = schema.safeParse(data);
      const duration = timer.end({
        validation_type: 'request',
        endpoint: context.endpoint,
      });

      if (result.success) {
        span.setAttributes({
          validation_result: 'success',
          [TELEMETRY_ATTRIBUTES.DURATION_MS]: duration,
        });
        
        enhancedTelemetry.recordCounter('runtime_guard.validations.success', 1, {
          validation_type: 'request',
          endpoint: context.endpoint,
        });

        span.end();
        return {
          valid: true,
          data: result.data,
          violations: [],
        };
      } else {
        const violation = this.createValidationViolation(
          result.error,
          context,
          ViolationSeverity.MEDIUM
        );

        span.recordException(new Error(violation.message));
        span.setAttributes({
          validation_result: 'failure',
          violation_count: result.error.issues.length,
          [TELEMETRY_ATTRIBUTES.ERROR_TYPE]: ViolationType.SCHEMA_VALIDATION,
          [TELEMETRY_ATTRIBUTES.DURATION_MS]: duration,
        });

        this.violations.push(violation);
        this.recordViolation(violation);

        span.end();
        return {
          valid: false,
          violations: [violation],
        };
      }
    } catch (error) {
      span.recordException(error as Error);
      span.setAttributes({
        validation_result: 'error',
        [TELEMETRY_ATTRIBUTES.ERROR_TYPE]: 'validation_error',
      });
      span.end();
      throw error;
    }
  }

  /**
   * Validate response data against Zod schema
   */
  public validateResponse<T>(
    schema: z.ZodSchema<T>,
    data: unknown,
    context: {
      requestId?: string;
      endpoint?: string;
      statusCode?: number;
    } = {}
  ): ValidationResult {
    const span = this.tracer.startSpan('runtime_guard.validate_response', {
      attributes: {
        [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'runtime-guard',
        [TELEMETRY_ATTRIBUTES.SERVICE_OPERATION]: 'validate_response',
        [TELEMETRY_ATTRIBUTES.REQUEST_ID]: context.requestId || 'unknown',
        endpoint: context.endpoint || 'unknown',
        status_code: context.statusCode || 0,
      },
    });

    try {
      const timer = enhancedTelemetry.createTimer('runtime_guard.validation.duration');
      const result = schema.safeParse(data);
      const duration = timer.end({
        validation_type: 'response',
        endpoint: context.endpoint,
      });

      if (result.success) {
        span.setAttributes({
          validation_result: 'success',
          [TELEMETRY_ATTRIBUTES.DURATION_MS]: duration,
        });

        enhancedTelemetry.recordCounter('runtime_guard.validations.success', 1, {
          validation_type: 'response',
          endpoint: context.endpoint,
        });

        span.end();
        return {
          valid: true,
          data: result.data,
          violations: [],
        };
      } else {
        const violation = this.createValidationViolation(
          result.error,
          context,
          ViolationSeverity.HIGH // Response validation failures are more serious
        );

        span.recordException(new Error(violation.message));
        span.setAttributes({
          validation_result: 'failure',
          violation_count: result.error.issues.length,
          [TELEMETRY_ATTRIBUTES.ERROR_TYPE]: ViolationType.SCHEMA_VALIDATION,
          [TELEMETRY_ATTRIBUTES.DURATION_MS]: duration,
        });

        this.violations.push(violation);
        this.recordViolation(violation);

        span.end();
        return {
          valid: false,
          violations: [violation],
        };
      }
    } catch (error) {
      span.recordException(error as Error);
      span.end();
      throw error;
    }
  }

  /**
   * Record business rule violation
   */
  public recordBusinessRuleViolation(
    rule: string,
    message: string,
    severity: ViolationSeverity = ViolationSeverity.MEDIUM,
    details?: Record<string, any>
  ): ContractViolation {
    const violation: ContractViolation = {
      id: `biz_rule_${Date.now()}_${Math.random().toString(36).substring(2, 11)}`,
      type: ViolationType.BUSINESS_RULE,
      severity,
      message: `Business rule violation: ${rule} - ${message}`,
      timestamp: new Date(),
      details: { rule, ...details },
    };

    this.violations.push(violation);
    this.recordViolation(violation);

    return violation;
  }

  /**
   * Record rate limit violation
   */
  public recordRateLimitViolation(
    endpoint: string,
    limit: number,
    current: number,
    windowMs: number,
    requestId?: string
  ): ContractViolation {
    const violation: ContractViolation = {
      id: `rate_limit_${Date.now()}_${Math.random().toString(36).substring(2, 11)}`,
      type: ViolationType.RATE_LIMIT,
      severity: ViolationSeverity.MEDIUM,
      message: `Rate limit exceeded for ${endpoint}: ${current}/${limit} requests in ${windowMs}ms`,
      timestamp: new Date(),
      ...(requestId ? { requestId } : {}),
      endpoint,
      details: { limit, current, windowMs },
    };

    this.violations.push(violation);
    this.recordViolation(violation);

    return violation;
  }

  /**
   * Create Fastify middleware for request validation
   */
  public createRequestValidator<T>(schema: z.ZodSchema<T>) {
    return async (request: FastifyRequest, reply: FastifyReply) => {
      const result = this.validateRequest(schema, request.body, {
        requestId: request.id,
        endpoint: `${request.method} ${request.url}`,
        operation: 'request_validation',
      });

      if (!result.valid) {
        const violation = result.violations[0];
        return reply.code(400).send({
          error: 'Validation Error',
          message: 'Request payload validation failed',
          details: violation?.details || 'Unknown validation error',
          violation_id: violation?.id || 'unknown',
        });
      }

      // Attach validated data to request
      (request as any).validatedBody = result.data;
    };
  }

  /**
   * Create Fastify middleware for response validation
   */
  public createResponseValidator<T>(schema: z.ZodSchema<T>) {
    return async (request: FastifyRequest, reply: FastifyReply, payload: any) => {
      const result = this.validateResponse(schema, payload, {
        requestId: request.id,
        endpoint: `${request.method} ${request.url}`,
        statusCode: reply.statusCode,
      });

      if (!result.valid) {
        // Log the violation but don't modify the response in production
        // to avoid breaking the API contract
        const violation = result.violations[0];
        console.error('Response validation failed:', violation);
        
        if (process.env['NODE_ENV'] === 'development') {
          return {
            error: 'Response Validation Error',
            message: 'Response payload validation failed',
            details: violation?.details || 'Unknown validation error',
            violation_id: violation?.id || 'unknown',
            original_payload: payload,
          };
        }
      }

      return payload;
    };
  }

  /**
   * Get all violations within a time window
   */
  public getViolations(since?: Date): ContractViolation[] {
    if (!since) return [...this.violations];
    
    return this.violations.filter(v => v.timestamp >= since);
  }

  /**
   * Get violation statistics
   */
  public getViolationStats(): ViolationStats {
    const now = new Date();
    const last24Threshold = new Date(now.getTime() - 24 * HOUR_IN_MS);

    const initializeByType = () => Object.values(ViolationType).reduce((acc, type) => {
      acc[type] = 0;
      return acc;
    }, {} as Record<ViolationType, number>);

    const initializeBySeverity = () => Object.values(ViolationSeverity).reduce((acc, severity) => {
      acc[severity] = 0;
      return acc;
    }, {} as Record<ViolationSeverity, number>);

    const byType = initializeByType();
    const bySeverity = initializeBySeverity();
    const byEndpoint = new Map<string, number>();
    const last24ByType = initializeByType();
    const last24BySeverity = initializeBySeverity();
    const hourlyBuckets = new Map<string, number>();

    let last24Total = 0;

    for (const violation of this.violations) {
      byType[violation.type] += 1;
      bySeverity[violation.severity] += 1;

      const endpointKey = violation.endpoint ?? 'unknown';
      byEndpoint.set(endpointKey, (byEndpoint.get(endpointKey) ?? 0) + 1);
    }

    for (let idx = this.violations.length - 1; idx >= 0; idx -= 1) {
      const violation = this.violations[idx];
      if (violation.timestamp < last24Threshold) {
        break;
      }

      last24Total += 1;
      last24ByType[violation.type] += 1;
      last24BySeverity[violation.severity] += 1;

      const bucketTime = new Date(Math.floor(violation.timestamp.getTime() / HOUR_IN_MS) * HOUR_IN_MS);
      const bucketKey = bucketTime.toISOString();
      hourlyBuckets.set(bucketKey, (hourlyBuckets.get(bucketKey) ?? 0) + 1);
    }

    const byEndpointObject = Array.from(byEndpoint.entries())
      .sort((a, b) => b[1] - a[1])
      .reduce((acc, [key, value]) => {
        acc[key] = value;
        return acc;
      }, {} as Record<string, number>);

    const hourlyBucketsArray: HourlyViolationBucket[] = Array.from(hourlyBuckets.entries())
      .sort((a, b) => a[0].localeCompare(b[0]))
      .map(([hour, count]) => ({ hour, count }));

    const recent: ViolationStats['recent'] = [];
    for (let idx = this.violations.length - 1; idx >= 0 && recent.length < 10; idx -= 1) {
      const violation = this.violations[idx];
      recent.push({
        id: violation.id,
        type: violation.type,
        severity: violation.severity,
        endpoint: violation.endpoint ?? null,
        timestamp: violation.timestamp.toISOString(),
      });
    }

    return {
      total: this.violations.length,
      byType,
      bySeverity,
      byEndpoint: byEndpointObject,
      last24Hours: {
        total: last24Total,
        byType: last24ByType,
        bySeverity: last24BySeverity,
        hourlyBuckets: hourlyBucketsArray,
      },
      recent,
    };
  }

  /**
   * Clear old violations (cleanup)
   */
  public clearOldViolations(olderThan: Date): number {
    const initialCount = this.violations.length;
    this.violations = this.violations.filter(v => v.timestamp >= olderThan);
    return initialCount - this.violations.length;
  }

  private createValidationViolation(
    error: z.ZodError,
    context: { requestId?: string; endpoint?: string },
    severity: ViolationSeverity
  ): ContractViolation {
    const issues = error.issues.map(issue => ({
      path: issue.path.join('.'),
      message: issue.message,
      code: issue.code,
    }));

    return {
      id: `validation_${Date.now()}_${Math.random().toString(36).substring(2, 11)}`,
      type: ViolationType.SCHEMA_VALIDATION,
      severity,
      message: `Schema validation failed: ${issues.length} issues found`,
      timestamp: new Date(),
      ...(context.requestId ? { requestId: context.requestId } : {}),
      ...(context.endpoint ? { endpoint: context.endpoint } : {}),
      details: { issues },
    };
  }

  private recordViolation(violation: ContractViolation): void {
    enhancedTelemetry.recordContractViolation(
      violation.type,
      violation.id,
      violation.severity,
      {
        endpoint: violation.endpoint,
        request_id: violation.requestId,
        violation_message: violation.message,
      }
    );

    enhancedTelemetry.recordCounter('runtime_guard.violations.total', 1, {
      violation_type: violation.type,
      severity: violation.severity,
      endpoint: violation.endpoint,
    });
  }
}

// Global runtime guard instance
export const runtimeGuard = new RuntimeGuard();

// Common validation schemas
export const CommonSchemas = {
  // Health check response
  HealthResponse: z.object({
    status: z.literal('healthy'),
    timestamp: z.string(),
    service: z.string(),
  }),

  // Error response
  ErrorResponse: z.object({
    error: z.string(),
    message: z.string().optional(),
    details: z.record(z.any()).optional(),
  }),

  // Reservation request
  ReservationRequest: z.object({
    orderId: z.string().min(1),
    itemId: z.string().min(1),
    quantity: z.number().int().positive(),
  }),

  // Reservation response
  ReservationResponse: z.object({
    ok: z.boolean(),
    reservationId: z.string().optional(),
  }),
} as const;
