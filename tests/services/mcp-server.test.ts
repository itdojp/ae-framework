import { describe, test, expect, beforeEach, vi, afterEach } from 'vitest';
import { MCPServer, MCPServerConfig, MCPPlugin, MCPRequest, MCPResponse } from '../../src/services/mcp-server.js';
import { EventEmitter } from 'events';

describe('MCPServer', () => {
  let server: MCPServer;
  let mockConfig: MCPServerConfig;
  const testProjectRoot = '/test/project';

  beforeEach(() => {
    vi.clearAllMocks();

    mockConfig = {
      name: 'test-server',
      version: '1.0.0',
      description: 'Test MCP Server',
      endpoints: [],
      capabilities: [
        { name: 'health-check', version: '1.0.0', enabled: true },
        { name: 'metrics', version: '1.0.0', enabled: true }
      ]
    };

    server = new MCPServer(mockConfig, testProjectRoot);
  });

  afterEach(() => {
    if (server) {
      server.stop().catch(() => {});
    }
  });

  describe('Server Lifecycle', () => {
    test('should start server successfully', async () => {
      const startedSpy = vi.fn();
      server.on('started', startedSpy);

      await server.start();

      expect(startedSpy).toHaveBeenCalledWith({
        server: 'test-server',
        timestamp: expect.any(Number)
      });

      const status = server.getStatus();
      expect(status.running).toBe(true);
      expect(status.config.name).toBe('test-server');
    });

    test('should not start server twice', async () => {
      await server.start();

      await expect(server.start()).rejects.toThrow('Server is already running');
    });

    test('should stop server successfully', async () => {
      const stoppedSpy = vi.fn();
      server.on('stopped', stoppedSpy);

      await server.start();
      await server.stop();

      expect(stoppedSpy).toHaveBeenCalledWith({
        server: 'test-server',
        timestamp: expect.any(Number)
      });

      const status = server.getStatus();
      expect(status.running).toBe(false);
    });

    test('should not error when stopping non-running server', async () => {
      await expect(server.stop()).resolves.not.toThrow();
    });
  });

  describe('Default Endpoints', () => {
    beforeEach(async () => {
      await server.start();
    });

    test('should register default health endpoint', async () => {
      const request: MCPRequest = {
        path: '/health',
        method: 'GET',
        params: {},
        headers: {},
        context: {
          requestId: 'test-1',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(200);
      expect(response.data).toEqual({
        status: 'healthy',
        uptime: expect.any(Number),
        timestamp: expect.any(Number)
      });
    });

    test('should register default metrics endpoint', async () => {
      const request: MCPRequest = {
        path: '/metrics',
        method: 'GET',
        params: {},
        headers: {},
        context: {
          requestId: 'test-2',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(200);
      expect(response.data).toHaveProperty('requestCount');
      expect(response.data).toHaveProperty('errorCount');
      expect(response.data).toHaveProperty('averageResponseTime');
    });

    test('should register default capabilities endpoint', async () => {
      const request: MCPRequest = {
        path: '/capabilities',
        method: 'GET',
        params: {},
        headers: {},
        context: {
          requestId: 'test-3',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(200);
      expect(Array.isArray(response.data)).toBe(true);
      expect(response.data.length).toBeGreaterThan(0);
    });
  });

  describe('Custom Endpoints', () => {
    test('should register custom endpoint', async () => {
      const customEndpoint = {
        path: '/custom',
        method: 'GET' as const,
        handler: async (request: MCPRequest): Promise<MCPResponse> => ({
          status: 200,
          data: { message: 'Custom endpoint response' }
        }),
        description: 'Custom test endpoint'
      };

      server.registerEndpoint(customEndpoint);
      await server.start();

      const request: MCPRequest = {
        path: '/custom',
        method: 'GET',
        params: {},
        headers: {},
        context: {
          requestId: 'test-4',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(200);
      expect(response.data.message).toBe('Custom endpoint response');
    });

    test('should not register duplicate endpoints', () => {
      const endpoint1 = {
        path: '/duplicate',
        method: 'GET' as const,
        handler: async () => ({ status: 200 })
      };

      const endpoint2 = {
        path: '/duplicate',
        method: 'GET' as const,
        handler: async () => ({ status: 200 })
      };

      server.registerEndpoint(endpoint1);
      
      expect(() => server.registerEndpoint(endpoint2))
        .toThrow('Endpoint GET:/duplicate is already registered');
    });

    test('should return 404 for non-existent endpoints', async () => {
      await server.start();

      const request: MCPRequest = {
        path: '/non-existent',
        method: 'GET',
        params: {},
        headers: {},
        context: {
          requestId: 'test-5',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(404);
      expect(response.error).toBe('Endpoint not found');
    });
  });

  describe('Plugin Management', () => {
    test('should register plugin successfully', async () => {
      const mockPlugin: MCPPlugin = {
        name: 'test-plugin',
        version: '1.0.0',
        description: 'Test plugin',
        initialize: vi.fn().mockResolvedValue(undefined),
        endpoints: [
          {
            path: '/plugin-test',
            method: 'GET',
            handler: async () => ({ status: 200, data: { plugin: 'test' } })
          }
        ]
      };

      const pluginRegisteredSpy = vi.fn();
      server.on('plugin-registered', pluginRegisteredSpy);

      await server.registerPlugin(mockPlugin);

      expect(mockPlugin.initialize).toHaveBeenCalledWith(server);
      expect(pluginRegisteredSpy).toHaveBeenCalledWith({
        plugin: 'test-plugin',
        timestamp: expect.any(Number)
      });

      const metrics = server.getMetrics();
      expect(metrics.pluginsLoaded).toBe(1);
      expect(metrics.endpointsRegistered).toBeGreaterThan(0);
    });

    test('should not register duplicate plugins', async () => {
      const mockPlugin: MCPPlugin = {
        name: 'duplicate-plugin',
        version: '1.0.0',
        initialize: vi.fn().mockResolvedValue(undefined)
      };

      await server.registerPlugin(mockPlugin);

      await expect(server.registerPlugin(mockPlugin))
        .rejects.toThrow('Plugin duplicate-plugin is already registered');
    });

    test('should check plugin dependencies', async () => {
      const dependentPlugin: MCPPlugin = {
        name: 'dependent-plugin',
        version: '1.0.0',
        dependencies: ['missing-dependency'],
        initialize: vi.fn().mockResolvedValue(undefined)
      };

      await expect(server.registerPlugin(dependentPlugin))
        .rejects.toThrow('Plugin dependent-plugin requires dependency missing-dependency');
    });

    test('should terminate plugins on server stop', async () => {
      const terminateSpy = vi.fn().mockResolvedValue(undefined);
      const mockPlugin: MCPPlugin = {
        name: 'terminatable-plugin',
        version: '1.0.0',
        initialize: vi.fn().mockResolvedValue(undefined),
        terminate: terminateSpy
      };

      await server.registerPlugin(mockPlugin);
      await server.start();
      await server.stop();

      expect(terminateSpy).toHaveBeenCalledWith(server);
    });
  });

  describe('Request Processing', () => {
    beforeEach(async () => {
      await server.start();
    });

    test('should update metrics on request processing', async () => {
      const initialMetrics = server.getMetrics();

      const request: MCPRequest = {
        path: '/health',
        method: 'GET',
        params: {},
        headers: {},
        context: {
          requestId: 'test-6',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      await server.processRequest(request);

      const updatedMetrics = server.getMetrics();
      expect(updatedMetrics.requestCount).toBe(initialMetrics.requestCount + 1);
      expect(updatedMetrics.averageResponseTime).toBeGreaterThanOrEqual(0);
    });

    test('should handle request errors gracefully', async () => {
      server.registerEndpoint({
        path: '/error',
        method: 'GET',
        handler: async () => {
          throw new Error('Test error');
        }
      });

      const request: MCPRequest = {
        path: '/error',
        method: 'GET',
        params: {},
        headers: {},
        context: {
          requestId: 'test-7',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(500);
      expect(response.error).toContain('Internal server error');

      const metrics = server.getMetrics();
      expect(metrics.errorCount).toBeGreaterThan(0);
    });
  });

  describe('Capabilities', () => {
    test('should get server capabilities', async () => {
      const capabilities = server.getCapabilities();

      expect(Array.isArray(capabilities)).toBe(true);
      expect(capabilities.find(c => c.name === 'health-check')).toBeDefined();
      expect(capabilities.find(c => c.name === 'metrics')).toBeDefined();
    });

    test('should enable/disable capabilities', async () => {
      const capabilityChangedSpy = vi.fn();
      server.on('capability-changed', capabilityChangedSpy);

      server.setCapability('health-check', false);

      const capabilities = server.getCapabilities();
      const healthCheck = capabilities.find(c => c.name === 'health-check');
      
      expect(healthCheck?.enabled).toBe(false);
      expect(capabilityChangedSpy).toHaveBeenCalledWith({
        capability: 'health-check',
        enabled: false,
        timestamp: expect.any(Number)
      });
    });
  });

  describe('Validation', () => {
    test('should validate required parameters', async () => {
      server.registerEndpoint({
        path: '/validate',
        method: 'POST',
        handler: async () => ({ status: 200 }),
        parameters: [
          {
            name: 'required-param',
            type: 'string',
            required: true
          }
        ]
      });

      await server.start();

      const request: MCPRequest = {
        path: '/validate',
        method: 'POST',
        params: {},
        body: {},
        headers: {},
        context: {
          requestId: 'test-8',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(400);
      expect(response.error).toContain('Required parameter \'required-param\' is missing');
    });

    test('should validate parameter constraints', async () => {
      server.registerEndpoint({
        path: '/validate-min',
        method: 'POST',
        handler: async () => ({ status: 200 }),
        parameters: [
          {
            name: 'min-param',
            type: 'string',
            required: true,
            validation: [
              { type: 'min', value: 5, message: 'Must be at least 5 characters' }
            ]
          }
        ]
      });

      await server.start();

      const request: MCPRequest = {
        path: '/validate-min',
        method: 'POST',
        params: { 'min-param': 'abc' },
        headers: {},
        context: {
          requestId: 'test-9',
          timestamp: Date.now(),
          serverName: 'test-server',
          version: '1.0.0',
          environment: 'testing',
          projectRoot: testProjectRoot
        }
      };

      const response = await server.processRequest(request);

      expect(response.status).toBe(400);
      expect(response.error).toBe('Must be at least 5 characters');
    });
  });
});