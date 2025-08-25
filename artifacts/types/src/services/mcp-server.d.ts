/**
 * MCP Server Extensions for ae-framework
 * Provides extensible server capabilities and plugin architecture
 */
import { EventEmitter } from 'events';
export interface MCPServerConfig {
    name: string;
    version: string;
    description?: string;
    endpoints: MCPEndpoint[];
    middleware?: MCPMiddleware[];
    plugins?: MCPPlugin[];
    capabilities: MCPCapability[];
    authentication?: MCPAuthConfig;
    rateLimit?: MCPRateLimitConfig;
}
export interface MCPEndpoint {
    path: string;
    method: 'GET' | 'POST' | 'PUT' | 'DELETE' | 'PATCH';
    handler: MCPEndpointHandler;
    description?: string;
    parameters?: MCPParameter[];
    response?: MCPResponseSchema;
    authentication?: boolean;
    rateLimit?: number;
}
export interface MCPParameter {
    name: string;
    type: 'string' | 'number' | 'boolean' | 'object' | 'array';
    required: boolean;
    description?: string;
    validation?: MCPValidationRule[];
}
export interface MCPValidationRule {
    type: 'min' | 'max' | 'pattern' | 'enum' | 'custom';
    value: any;
    message?: string;
}
export interface MCPResponseSchema {
    type: 'object' | 'array' | 'string' | 'number' | 'boolean';
    properties?: Record<string, MCPParameter>;
    items?: MCPParameter;
}
export type MCPEndpointHandler = (request: MCPRequest) => Promise<MCPResponse>;
export interface MCPRequest {
    path: string;
    method: string;
    params: Record<string, any>;
    body?: any;
    headers: Record<string, string>;
    user?: MCPUser;
    context: MCPContext;
}
export interface MCPResponse {
    status: number;
    data?: any;
    error?: string;
    headers?: Record<string, string>;
    metadata?: Record<string, any>;
}
export interface MCPContext {
    requestId: string;
    timestamp: number;
    serverName: string;
    version: string;
    environment: 'development' | 'production' | 'testing';
    projectRoot: string;
}
export interface MCPUser {
    id: string;
    name: string;
    roles: string[];
    permissions: string[];
}
export interface MCPMiddleware {
    name: string;
    handler: MCPMiddlewareHandler;
    order?: number;
}
export type MCPMiddlewareHandler = (request: MCPRequest, response: MCPResponse, next: () => Promise<void>) => Promise<void>;
export interface MCPPlugin {
    name: string;
    version: string;
    description?: string;
    initialize: (server: MCPServer) => Promise<void>;
    terminate?: (server: MCPServer) => Promise<void>;
    dependencies?: string[];
    endpoints?: MCPEndpoint[];
    middleware?: MCPMiddleware[];
}
export interface MCPCapability {
    name: string;
    version: string;
    description?: string;
    enabled: boolean;
    configuration?: Record<string, any>;
}
export interface MCPAuthConfig {
    type: 'jwt' | 'apikey' | 'basic' | 'custom';
    configuration: Record<string, any>;
}
export interface MCPRateLimitConfig {
    windowMs: number;
    maxRequests: number;
    skipSuccessfulRequests?: boolean;
    skipFailedRequests?: boolean;
}
export interface MCPServerMetrics {
    requestCount: number;
    errorCount: number;
    averageResponseTime: number;
    uptime: number;
    activeConnections: number;
    pluginsLoaded: number;
    endpointsRegistered: number;
}
export declare class MCPServer extends EventEmitter {
    private config;
    private endpoints;
    private middleware;
    private plugins;
    private capabilities;
    private isRunning;
    private startTime;
    private metrics;
    private totalResponseTime;
    private projectRoot;
    constructor(config: MCPServerConfig, projectRoot: string);
    /**
     * Start the MCP server
     */
    start(): Promise<void>;
    /**
     * Stop the MCP server
     */
    stop(): Promise<void>;
    /**
     * Process an incoming request
     */
    processRequest(request: MCPRequest): Promise<MCPResponse>;
    /**
     * Register a plugin
     */
    registerPlugin(plugin: MCPPlugin): Promise<void>;
    /**
     * Register an endpoint
     */
    registerEndpoint(endpoint: MCPEndpoint): void;
    /**
     * Register middleware
     */
    registerMiddlewareItem(middleware: MCPMiddleware): void;
    /**
     * Get server capabilities
     */
    getCapabilities(): MCPCapability[];
    /**
     * Enable/disable capability
     */
    setCapability(name: string, enabled: boolean): void;
    /**
     * Get server metrics
     */
    getMetrics(): MCPServerMetrics;
    /**
     * Get server status
     */
    getStatus(): {
        running: boolean;
        uptime: number;
        config: MCPServerConfig;
    };
    private setupDefaultCapabilities;
    private loadPlugins;
    private registerMiddleware;
    private registerEndpoints;
    private setupDefaultEndpoints;
    private runMiddleware;
    private validateRequest;
    private validateValue;
}
/**
 * Factory function to create MCP server with Rust verification plugin
 */
export declare function createRustVerificationServer(projectRoot: string): Promise<MCPServer>;
