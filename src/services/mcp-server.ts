/**
 * MCP Server Extensions for ae-framework
 * Provides extensible server capabilities and plugin architecture
 */

import * as fs from 'fs/promises';
import * as path from 'path';
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

export type MCPMiddlewareHandler = (
  request: MCPRequest, 
  response: MCPResponse, 
  next: () => Promise<void>
) => Promise<void>;

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

export class MCPServer extends EventEmitter {
  private config: MCPServerConfig;
  private endpoints: Map<string, MCPEndpoint> = new Map();
  private middleware: MCPMiddleware[] = [];
  private plugins: Map<string, MCPPlugin> = new Map();
  private capabilities: Map<string, MCPCapability> = new Map();
  private isRunning: boolean = false;
  private startTime: number = 0;
  private metrics: MCPServerMetrics = {
    requestCount: 0,
    errorCount: 0,
    averageResponseTime: 0,
    uptime: 0,
    activeConnections: 0,
    pluginsLoaded: 0,
    endpointsRegistered: 0
  };
  private totalResponseTime: number = 0;
  private projectRoot: string;

  constructor(config: MCPServerConfig, projectRoot: string) {
    super();
    this.config = config;
    this.projectRoot = projectRoot;
    this.setupDefaultCapabilities();
  }

  /**
   * Start the MCP server
   */
  async start(): Promise<void> {
    if (this.isRunning) {
      throw new Error('Server is already running');
    }

    try {
      this.startTime = Date.now();
      
      // Load and initialize plugins
      await this.loadPlugins();
      
      // Register middleware
      this.registerMiddleware();
      
      // Register endpoints
      this.registerEndpoints();
      
      // Setup default endpoints
      this.setupDefaultEndpoints();
      
      this.isRunning = true;
      this.emit('started', { server: this.config.name, timestamp: Date.now() });
      
    } catch (error: any) {
      this.emit('error', { error: error.message, timestamp: Date.now() });
      throw error;
    }
  }

  /**
   * Stop the MCP server
   */
  async stop(): Promise<void> {
    if (!this.isRunning) {
      return;
    }

    try {
      // Terminate plugins
      for (const plugin of this.plugins.values()) {
        if (plugin.terminate) {
          await plugin.terminate(this);
        }
      }

      this.isRunning = false;
      this.emit('stopped', { server: this.config.name, timestamp: Date.now() });
      
    } catch (error: any) {
      this.emit('error', { error: error.message, timestamp: Date.now() });
      throw error;
    }
  }

  /**
   * Process an incoming request
   */
  async processRequest(request: MCPRequest): Promise<MCPResponse> {
    const startTime = Date.now();
    this.metrics.requestCount++;

    try {
      // Create response object
      const response: MCPResponse = {
        status: 200,
        data: null
      };

      // Run middleware chain
      await this.runMiddleware(request, response);

      // Find and execute endpoint handler
      const endpointKey = `${request.method}:${request.path}`;
      const endpoint = this.endpoints.get(endpointKey);

      if (!endpoint) {
        response.status = 404;
        response.error = 'Endpoint not found';
        this.metrics.errorCount++;
        return response;
      }

      // Validate request parameters
      const validationError = this.validateRequest(request, endpoint);
      if (validationError) {
        response.status = 400;
        response.error = validationError;
        this.metrics.errorCount++;
        return response;
      }

      // Check authentication if required
      if (endpoint.authentication && !request.user) {
        response.status = 401;
        response.error = 'Authentication required';
        this.metrics.errorCount++;
        return response;
      }

      // Execute endpoint handler
      const handlerResponse = await endpoint.handler(request);
      Object.assign(response, handlerResponse);

      return response;

    } catch (error: any) {
      this.metrics.errorCount++;
      return {
        status: 500,
        error: `Internal server error: ${error.message}`
      };

    } finally {
      // Update metrics
      const responseTime = Date.now() - startTime;
      this.totalResponseTime += responseTime;
      this.metrics.averageResponseTime = this.totalResponseTime / this.metrics.requestCount;
      this.metrics.uptime = Date.now() - this.startTime;
    }
  }

  /**
   * Register a plugin
   */
  async registerPlugin(plugin: MCPPlugin): Promise<void> {
    if (this.plugins.has(plugin.name)) {
      throw new Error(`Plugin ${plugin.name} is already registered`);
    }

    // Check dependencies
    if (plugin.dependencies) {
      for (const dep of plugin.dependencies) {
        if (!this.plugins.has(dep)) {
          throw new Error(`Plugin ${plugin.name} requires dependency ${dep}`);
        }
      }
    }

    // Initialize plugin
    await plugin.initialize(this);

    // Register plugin endpoints
    if (plugin.endpoints) {
      for (const endpoint of plugin.endpoints) {
        this.registerEndpoint(endpoint);
      }
    }

    // Register plugin middleware
    if (plugin.middleware) {
      for (const middleware of plugin.middleware) {
        this.registerMiddlewareItem(middleware);
      }
    }

    this.plugins.set(plugin.name, plugin);
    this.metrics.pluginsLoaded++;
    
    this.emit('plugin-registered', { plugin: plugin.name, timestamp: Date.now() });
  }

  /**
   * Register an endpoint
   */
  registerEndpoint(endpoint: MCPEndpoint): void {
    const key = `${endpoint.method}:${endpoint.path}`;
    
    if (this.endpoints.has(key)) {
      throw new Error(`Endpoint ${key} is already registered`);
    }

    this.endpoints.set(key, endpoint);
    this.metrics.endpointsRegistered++;
    
    this.emit('endpoint-registered', { 
      endpoint: key, 
      timestamp: Date.now() 
    });
  }

  /**
   * Register middleware
   */
  registerMiddlewareItem(middleware: MCPMiddleware): void {
    this.middleware.push(middleware);
    this.middleware.sort((a, b) => (a.order || 0) - (b.order || 0));
    
    this.emit('middleware-registered', { 
      middleware: middleware.name, 
      timestamp: Date.now() 
    });
  }

  /**
   * Get server capabilities
   */
  getCapabilities(): MCPCapability[] {
    return Array.from(this.capabilities.values());
  }

  /**
   * Enable/disable capability
   */
  setCapability(name: string, enabled: boolean): void {
    const capability = this.capabilities.get(name);
    if (capability) {
      capability.enabled = enabled;
      this.emit('capability-changed', { 
        capability: name, 
        enabled, 
        timestamp: Date.now() 
      });
    }
  }

  /**
   * Get server metrics
   */
  getMetrics(): MCPServerMetrics {
    return { ...this.metrics };
  }

  /**
   * Get server status
   */
  getStatus(): { running: boolean; uptime: number; config: MCPServerConfig } {
    return {
      running: this.isRunning,
      uptime: this.isRunning ? Date.now() - this.startTime : 0,
      config: this.config
    };
  }

  // Private methods

  private setupDefaultCapabilities(): void {
    const defaultCapabilities: MCPCapability[] = [
      {
        name: 'health-check',
        version: '1.0.0',
        description: 'Server health monitoring',
        enabled: true
      },
      {
        name: 'metrics',
        version: '1.0.0',
        description: 'Performance metrics collection',
        enabled: true
      },
      {
        name: 'plugin-management',
        version: '1.0.0',
        description: 'Dynamic plugin loading and management',
        enabled: true
      },
      {
        name: 'authentication',
        version: '1.0.0',
        description: 'Request authentication',
        enabled: !!this.config.authentication
      }
    ];

    for (const capability of defaultCapabilities) {
      this.capabilities.set(capability.name, capability);
    }
  }

  private async loadPlugins(): Promise<void> {
    if (!this.config.plugins) return;

    for (const plugin of this.config.plugins) {
      await this.registerPlugin(plugin);
    }
  }

  private registerMiddleware(): void {
    if (!this.config.middleware) return;

    for (const middleware of this.config.middleware) {
      this.registerMiddlewareItem(middleware);
    }
  }

  private registerEndpoints(): void {
    for (const endpoint of this.config.endpoints) {
      this.registerEndpoint(endpoint);
    }
  }

  private setupDefaultEndpoints(): void {
    // Health check endpoint
    this.registerEndpoint({
      path: '/health',
      method: 'GET',
      handler: async () => ({
        status: 200,
        data: {
          status: 'healthy',
          uptime: this.metrics.uptime,
          timestamp: Date.now()
        }
      }),
      description: 'Server health check'
    });

    // Metrics endpoint
    this.registerEndpoint({
      path: '/metrics',
      method: 'GET',
      handler: async () => ({
        status: 200,
        data: this.getMetrics()
      }),
      description: 'Server performance metrics'
    });

    // Capabilities endpoint
    this.registerEndpoint({
      path: '/capabilities',
      method: 'GET',
      handler: async () => ({
        status: 200,
        data: this.getCapabilities()
      }),
      description: 'Server capabilities'
    });

    // Plugin list endpoint
    this.registerEndpoint({
      path: '/plugins',
      method: 'GET',
      handler: async () => ({
        status: 200,
        data: Array.from(this.plugins.keys())
      }),
      description: 'Loaded plugins list'
    });
  }

  private async runMiddleware(request: MCPRequest, response: MCPResponse): Promise<void> {
    let index = 0;

    const next = async (): Promise<void> => {
      if (index >= this.middleware.length) return;
      
      const middleware = this.middleware[index++];
      if (middleware) {
        await middleware.handler(request, response, next);
      }
    };

    await next();
  }

  private validateRequest(request: MCPRequest, endpoint: MCPEndpoint): string | null {
    if (!endpoint.parameters) return null;

    for (const param of endpoint.parameters) {
      const value = request.params[param.name] || request.body?.[param.name];
      
      if (param.required && (value === undefined || value === null)) {
        return `Required parameter '${param.name}' is missing`;
      }

      if (value !== undefined && param.validation) {
        for (const rule of param.validation) {
          const error = this.validateValue(value, rule, param.name);
          if (error) return error;
        }
      }
    }

    return null;
  }

  private validateValue(value: any, rule: MCPValidationRule, paramName: string): string | null {
    switch (rule.type) {
      case 'min':
        if (typeof value === 'string' && value.length < rule.value) {
          return rule.message || `Parameter '${paramName}' must be at least ${rule.value} characters`;
        }
        if (typeof value === 'number' && value < rule.value) {
          return rule.message || `Parameter '${paramName}' must be at least ${rule.value}`;
        }
        break;

      case 'max':
        if (typeof value === 'string' && value.length > rule.value) {
          return rule.message || `Parameter '${paramName}' must be at most ${rule.value} characters`;
        }
        if (typeof value === 'number' && value > rule.value) {
          return rule.message || `Parameter '${paramName}' must be at most ${rule.value}`;
        }
        break;

      case 'pattern':
        if (typeof value === 'string' && !new RegExp(rule.value).test(value)) {
          return rule.message || `Parameter '${paramName}' format is invalid`;
        }
        break;

      case 'enum':
        if (!rule.value.includes(value)) {
          return rule.message || `Parameter '${paramName}' must be one of: ${rule.value.join(', ')}`;
        }
        break;
    }

    return null;
  }
}

/**
 * Factory function to create MCP server with Rust verification plugin
 */
export async function createRustVerificationServer(projectRoot: string): Promise<MCPServer> {
  const { RustVerificationPlugin } = await import('./plugins/rust-verification-plugin.js');
  
  const config: MCPServerConfig = {
    name: 'ae-framework-rust-verification',
    version: '1.0.0',
    description: 'ae-framework MCP server with enhanced Rust verification capabilities',
    endpoints: [],
    capabilities: [
      {
        name: 'rust-verification',
        version: '1.0.0',
        description: 'Enhanced Rust formal verification using multiple tools',
        enabled: true,
        configuration: {
          tools: ['prusti', 'kani', 'miri'],
          autoDiscovery: true
        }
      }
    ],
    plugins: [
      new RustVerificationPlugin({
        enabledTools: ['prusti', 'kani', 'miri'],
        defaultOptions: {
          timeout: 300,
          memoryLimit: 2048,
          unwindLimit: 10,
          strictMode: true,
          generateReport: true
        }
      })
    ]
  };

  const server = new MCPServer(config, projectRoot);
  
  return server;
}