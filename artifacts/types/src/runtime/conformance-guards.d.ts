/**
 * Runtime Conformance Guards
 *
 * Zod-based runtime validation with OpenTelemetry integration
 * for detecting contract mismatches and specification drift
 */
import { z } from 'zod';
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
export interface GuardConfig {
    enabled: boolean;
    failOnViolation: boolean;
    logViolations: boolean;
    generateArtifacts: boolean;
    telemetryEnabled: boolean;
    context?: Record<string, any>;
}
/**
 * Runtime Conformance Guard
 *
 * Validates data against Zod schemas with telemetry and error handling
 */
export declare class ConformanceGuard<T> {
    private schema;
    private schemaName;
    private config;
    constructor(schema: z.ZodSchema<T>, schemaName: string, config?: Partial<GuardConfig>);
    /**
     * Validate input data against schema
     */
    validateInput(data: unknown, context?: Record<string, any>): Promise<ConformanceResult<T>>;
    /**
     * Validate output data against schema
     */
    validateOutput(data: unknown, context?: Record<string, any>): Promise<ConformanceResult<T>>;
    /**
     * Core validation logic with telemetry
     */
    private validate;
    /**
     * Generate failure artifact for conformance violations
     */
    private generateFailureArtifact;
    /**
     * Sanitize data for logging (remove sensitive information)
     */
    private sanitizeForLogging;
    /**
     * Update guard configuration
     */
    updateConfig(newConfig: Partial<GuardConfig>): void;
    /**
     * Get current configuration
     */
    getConfig(): GuardConfig;
}
/**
 * Conformance Violation Error
 */
export declare class ConformanceViolationError extends Error {
    schemaName: string;
    direction: 'input' | 'output';
    validationErrors: string[];
    data: unknown;
    constructor(message: string, schemaName: string, direction: 'input' | 'output', validationErrors: string[], data: unknown);
}
/**
 * Factory for creating common guards
 */
export declare class GuardFactory {
    /**
     * Create API request guard
     */
    static apiRequest<T>(schema: z.ZodSchema<T>, operationId: string): ConformanceGuard<T>;
    /**
     * Create API response guard
     */
    static apiResponse<T>(schema: z.ZodSchema<T>, operationId: string): ConformanceGuard<T>;
    /**
     * Create database entity guard
     */
    static databaseEntity<T>(schema: z.ZodSchema<T>, entityName: string): ConformanceGuard<T>;
    /**
     * Create configuration guard
     */
    static configuration<T>(schema: z.ZodSchema<T>, configName: string): ConformanceGuard<T>;
    /**
     * Create event guard
     */
    static event<T>(schema: z.ZodSchema<T>, eventType: string): ConformanceGuard<T>;
}
/**
 * Decorator for automatic method validation
 */
export declare function ValidateInput<T>(guard: ConformanceGuard<T>): (target: any, propertyKey: string, descriptor: PropertyDescriptor) => PropertyDescriptor;
/**
 * Decorator for automatic output validation
 */
export declare function ValidateOutput<T>(guard: ConformanceGuard<T>): (target: any, propertyKey: string, descriptor: PropertyDescriptor) => PropertyDescriptor;
/**
 * Middleware factory for Express.js integration
 */
export declare function createExpressMiddleware<T>(guard: ConformanceGuard<T>, target?: 'body' | 'query' | 'params'): (req: any, res: any, next: any) => Promise<any>;
/**
 * Global conformance registry for schema management
 */
export declare class ConformanceRegistry {
    private static instance;
    private guards;
    private schemas;
    static getInstance(): ConformanceRegistry;
    /**
     * Register a schema with the registry
     */
    registerSchema<T>(name: string, schema: z.ZodSchema<T>): void;
    /**
     * Register a guard with the registry
     */
    registerGuard<T>(name: string, guard: ConformanceGuard<T>): void;
    /**
     * Get a guard by name
     */
    getGuard<T>(name: string): ConformanceGuard<T> | undefined;
    /**
     * Get a schema by name
     */
    getSchema<T>(name: string): z.ZodSchema<T> | undefined;
    /**
     * Create a guard from a registered schema
     */
    createGuard<T>(schemaName: string, guardName?: string, config?: Partial<GuardConfig>): ConformanceGuard<T> | null;
    /**
     * List all registered schemas
     */
    listSchemas(): string[];
    /**
     * List all registered guards
     */
    listGuards(): string[];
    /**
     * Clear all registrations
     */
    clear(): void;
}
