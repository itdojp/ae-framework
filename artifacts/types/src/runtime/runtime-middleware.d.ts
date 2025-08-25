/**
 * Runtime Conformance Middleware
 *
 * Express and Fastify middleware for automatic runtime contract validation
 * with OpenTelemetry integration and failure artifact generation
 */
import { Request, Response, NextFunction } from 'express';
import { FastifyInstance } from 'fastify';
import { z } from 'zod';
export interface MiddlewareConfig {
    enabled: boolean;
    strictMode: boolean;
    logErrors: boolean;
    generateArtifacts: boolean;
    includeRequestInfo: boolean;
    customErrorHandler?: (error: any, req: any, res: any) => void;
}
/**
 * Express Middleware Factory
 */
export declare class ExpressConformanceMiddleware {
    private config;
    constructor(config?: Partial<MiddlewareConfig>);
    /**
     * Validate request body
     */
    validateRequestBody<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => Promise<void>;
    /**
     * Validate query parameters
     */
    validateQueryParams<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => Promise<void>;
    /**
     * Validate path parameters
     */
    validatePathParams<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => Promise<void>;
    /**
     * Validate response data
     */
    validateResponse<T>(schema: z.ZodSchema<T>, operationId: string): (req: Request, res: Response, next: NextFunction) => void;
    /**
     * Combined request/response validation middleware
     */
    validate<TReq, TRes>(requestSchema: z.ZodSchema<TReq> | null, responseSchema: z.ZodSchema<TRes> | null, operationId: string, target?: 'body' | 'query' | 'params'): ((req: Request, res: Response, next: NextFunction) => void)[];
    private createValidationContext;
    private handleValidationError;
    private handleMiddlewareError;
}
/**
 * Fastify Plugin for Runtime Conformance
 */
export declare function fastifyConformancePlugin(fastify: FastifyInstance, options?: {
    config?: Partial<MiddlewareConfig>;
    schemas?: Record<string, z.ZodSchema<any>>;
}): Promise<void>;
/**
 * OpenAPI Integration Helper
 */
export declare class OpenAPIConformanceIntegration {
    private middleware;
    constructor(config?: Partial<MiddlewareConfig>);
    /**
     * Generate middleware from OpenAPI operation
     */
    generateMiddleware(operation: {
        operationId: string;
        requestBody?: {
            schema: z.ZodSchema<any>;
        };
        parameters?: Array<{
            schema: z.ZodSchema<any>;
            in: 'query' | 'path';
        }>;
        responses?: {
            [status: string]: {
                schema: z.ZodSchema<any>;
            };
        };
    }): any[];
}
/**
 * Global middleware registry
 */
export declare class MiddlewareRegistry {
    private static instance;
    private expressMiddleware;
    private registeredRoutes;
    constructor(config?: Partial<MiddlewareConfig>);
    static getInstance(config?: Partial<MiddlewareConfig>): MiddlewareRegistry;
    /**
     * Register a route with validation
     */
    registerRoute(path: string, method: string, operationId: string, schemas: {
        request?: z.ZodSchema<any>;
        response?: z.ZodSchema<any>;
        query?: z.ZodSchema<any>;
        params?: z.ZodSchema<any>;
    }): any[];
    /**
     * Get middleware for a route
     */
    getMiddleware(path: string, method: string): any[];
    /**
     * List all registered routes
     */
    listRoutes(): Array<{
        path: string;
        method: string;
        operationId: string;
    }>;
}
