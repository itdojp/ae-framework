/**
 * Runtime Guards with OpenTelemetry Integration
 * Implements comprehensive request/response validation with telemetry tracking
 */
import { z } from 'zod';
import { FastifyRequest, FastifyReply } from 'fastify';
export declare enum ViolationType {
    SCHEMA_VALIDATION = "schema_validation",
    RATE_LIMIT = "rate_limit",
    AUTHORIZATION = "authorization",
    BUSINESS_RULE = "business_rule",
    DATA_INTEGRITY = "data_integrity",
    TIMEOUT = "timeout"
}
export declare enum ViolationSeverity {
    LOW = "low",
    MEDIUM = "medium",
    HIGH = "high",
    CRITICAL = "critical"
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
export interface ValidationResult {
    valid: boolean;
    data?: any;
    violations: ContractViolation[];
}
export declare class RuntimeGuard {
    private tracer;
    private violations;
    /**
     * Validate request payload against Zod schema
     */
    validateRequest<T>(schema: z.ZodSchema<T>, data: unknown, context?: {
        requestId?: string;
        endpoint?: string;
        operation?: string;
    }): ValidationResult;
    /**
     * Validate response data against Zod schema
     */
    validateResponse<T>(schema: z.ZodSchema<T>, data: unknown, context?: {
        requestId?: string;
        endpoint?: string;
        statusCode?: number;
    }): ValidationResult;
    /**
     * Record business rule violation
     */
    recordBusinessRuleViolation(rule: string, message: string, severity?: ViolationSeverity, details?: Record<string, any>): ContractViolation;
    /**
     * Record rate limit violation
     */
    recordRateLimitViolation(endpoint: string, limit: number, current: number, windowMs: number, requestId?: string): ContractViolation;
    /**
     * Create Fastify middleware for request validation
     */
    createRequestValidator<T>(schema: z.ZodSchema<T>): (request: FastifyRequest, reply: FastifyReply) => Promise<never>;
    /**
     * Create Fastify middleware for response validation
     */
    createResponseValidator<T>(schema: z.ZodSchema<T>): (request: FastifyRequest, reply: FastifyReply, payload: any) => Promise<any>;
    /**
     * Get all violations within a time window
     */
    getViolations(since?: Date): ContractViolation[];
    /**
     * Get violation statistics
     */
    getViolationStats(): {
        total: number;
        byType: Record<ViolationType, number>;
        bySeverity: Record<ViolationSeverity, number>;
        last24Hours: number;
    };
    /**
     * Clear old violations (cleanup)
     */
    clearOldViolations(olderThan: Date): number;
    private createValidationViolation;
    private recordViolation;
}
export declare const runtimeGuard: RuntimeGuard;
export declare const CommonSchemas: {
    readonly HealthResponse: z.ZodObject<{
        status: z.ZodLiteral<"healthy">;
        timestamp: z.ZodString;
        service: z.ZodString;
    }, "strip", z.ZodTypeAny, {
        status?: "healthy";
        timestamp?: string;
        service?: string;
    }, {
        status?: "healthy";
        timestamp?: string;
        service?: string;
    }>;
    readonly ErrorResponse: z.ZodObject<{
        error: z.ZodString;
        message: z.ZodOptional<z.ZodString>;
        details: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodAny>>;
    }, "strip", z.ZodTypeAny, {
        message?: string;
        error?: string;
        details?: Record<string, any>;
    }, {
        message?: string;
        error?: string;
        details?: Record<string, any>;
    }>;
    readonly ReservationRequest: z.ZodObject<{
        orderId: z.ZodString;
        itemId: z.ZodString;
        quantity: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        orderId?: string;
        itemId?: string;
        quantity?: number;
    }, {
        orderId?: string;
        itemId?: string;
        quantity?: number;
    }>;
    readonly ReservationResponse: z.ZodObject<{
        ok: z.ZodBoolean;
        reservationId: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        ok?: boolean;
        reservationId?: string;
    }, {
        ok?: boolean;
        reservationId?: string;
    }>;
};
