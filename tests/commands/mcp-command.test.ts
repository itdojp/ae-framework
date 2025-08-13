import { describe, test, expect, beforeEach, vi } from 'vitest';
import { MCPCommand } from '../../src/commands/extended/mcp-command.js';
import { MCPServer } from '../../src/services/mcp-server.js';
import { MCPPluginManager } from '../../src/utils/mcp-plugin-manager.js';
import * as fs from 'fs/promises';

// Mock dependencies
vi.mock('fs/promises');
vi.mock('../../src/services/mcp-server.js');
vi.mock('../../src/utils/mcp-plugin-manager.js');

describe('MCPCommand', () => {
  let mcpCommand: MCPCommand;
  let mockServer: any;
  let mockPluginManager: any;
  const testContext = { projectRoot: '/test/project' };

  beforeEach(() => {
    vi.clearAllMocks();

    // Mock MCPServer
    mockServer = {
      start: vi.fn().mockResolvedValue(undefined),
      stop: vi.fn().mockResolvedValue(undefined),
      getStatus: vi.fn().mockReturnValue({
        running: true,
        uptime: 10000,
        config: {
          name: 'test-server',
          version: '1.0.0',
          description: 'Test server'
        }
      }),
      getMetrics: vi.fn().mockReturnValue({
        requestCount: 100,
        errorCount: 5,
        averageResponseTime: 50,
        uptime: 10000,
        activeConnections: 2,
        pluginsLoaded: 3,
        endpointsRegistered: 8
      }),
      getCapabilities: vi.fn().mockReturnValue([
        { name: 'health-check', version: '1.0.0', enabled: true, description: 'Health monitoring' },
        { name: 'metrics', version: '1.0.0', enabled: true, description: 'Metrics collection' }
      ]),
      setCapability: vi.fn()
    };
    vi.mocked(MCPServer).mockImplementation(() => mockServer);

    // Mock MCPPluginManager
    mockPluginManager = {
      setServer: vi.fn(),
      loadPluginsFromDirectory: vi.fn(),
      getLoadedPlugins: vi.fn(),
      discoverPlugins: vi.fn(),
      enablePlugin: vi.fn(),
      disablePlugin: vi.fn(),
      unloadPlugin: vi.fn(),
      createPluginTemplate: vi.fn()
    };
    vi.mocked(MCPPluginManager).mockImplementation(() => mockPluginManager);

    // Mock file system
    vi.mocked(fs.mkdir).mockResolvedValue(undefined);
    vi.mocked(fs.writeFile).mockResolvedValue(undefined);
    vi.mocked(fs.readFile).mockResolvedValue('{"name":"test-config","version":"1.0.0"}');

    mcpCommand = new MCPCommand();
  });

  describe('Command Registration', () => {
    test('should have correct command properties', () => {
      expect(mcpCommand.name).toBe('/ae:mcp');
      expect(mcpCommand.description).toContain('Manage MCP server');
      expect(mcpCommand.category).toBe('utility');
      expect(mcpCommand.aliases).toContain('/mcp');
      expect(mcpCommand.aliases).toContain('/server');
    });
  });

  describe('Server Management', () => {
    test('should start MCP server successfully', async () => {
      mockPluginManager.loadPluginsFromDirectory.mockResolvedValue([
        { success: true, plugin: { manifest: { name: 'plugin1' } } },
        { success: true, plugin: { manifest: { name: 'plugin2' } } }
      ]);

      const result = await mcpCommand.handler(['start'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('MCP Server started successfully');
      expect(result.message).toContain('Loaded 2 plugins');
      expect(mockServer.start).toHaveBeenCalled();
      expect(mockPluginManager.setServer).toHaveBeenCalledWith(mockServer);
    });

    test('should handle plugin loading failures during start', async () => {
      mockPluginManager.loadPluginsFromDirectory.mockResolvedValue([
        { success: true, plugin: { manifest: { name: 'plugin1' } } },
        { success: false, error: 'Failed to load plugin2' }
      ]);

      const result = await mcpCommand.handler(['start'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Loaded 1 plugins');
      expect(result.message).toContain('Failed to load 1 plugins');
      expect(result.message).toContain('Failed to load plugin2');
    });

    test('should stop MCP server successfully', async () => {
      // First create a server instance
      await mcpCommand.handler(['start'], testContext);
      
      const result = await mcpCommand.handler(['stop'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('MCP Server stopped successfully');
      expect(mockServer.stop).toHaveBeenCalled();
    });

    test('should handle stop when no server running', async () => {
      const result = await mcpCommand.handler(['stop'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toBe('No MCP server instance found');
    });

    test('should restart MCP server', async () => {
      // First start server
      await mcpCommand.handler(['start'], testContext);
      
      mockPluginManager.loadPluginsFromDirectory.mockResolvedValue([]);

      const result = await mcpCommand.handler(['restart'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('MCP Server restarted successfully');
      expect(mockServer.stop).toHaveBeenCalled();
      // Reset call count since mocks are shared and restart internally creates new server
    });
  });

  describe('Server Status', () => {
    test('should show server status when running', async () => {
      await mcpCommand.handler(['start'], testContext);

      const result = await mcpCommand.handler(['status'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('MCP Server Status');
      expect(result.message).toContain('test-server');
      expect(result.message).toContain('Running: true');
      expect(result.message).toContain('Requests: 100');
      expect(result.serverStatus).toBeDefined();
      expect(result.metrics).toBeDefined();
    });

    test('should show not running status when server stopped', async () => {
      const result = await mcpCommand.handler(['status'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('MCP Server is not running');
      expect(result.serverStatus.running).toBe(false);
    });
  });

  describe('Plugin Management', () => {
    test('should list loaded plugins', async () => {
      mockPluginManager.getLoadedPlugins.mockReturnValue([
        {
          manifest: { name: 'plugin1', version: '1.0.0', description: 'First plugin' },
          enabled: true,
          loadedAt: Date.now()
        },
        {
          manifest: { name: 'plugin2', version: '2.0.0', description: 'Second plugin' },
          enabled: false,
          loadedAt: Date.now()
        }
      ]);

      const result = await mcpCommand.handler(['plugins', 'list'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Loaded Plugins');
      expect(result.message).toContain('plugin1');
      expect(result.message).toContain('plugin2');
      expect(result.message).toContain('✅'); // enabled plugin
      expect(result.message).toContain('❌'); // disabled plugin
      expect(result.pluginList).toEqual(['plugin1', 'plugin2']);
    });

    test('should show empty plugin list', async () => {
      mockPluginManager.getLoadedPlugins.mockReturnValue([]);

      const result = await mcpCommand.handler(['plugins', 'list'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('No plugins loaded');
      expect(result.pluginList).toEqual([]);
    });

    test('should discover available plugins', async () => {
      mockPluginManager.discoverPlugins.mockResolvedValue([
        { name: 'available-plugin1', version: '1.0.0', description: 'Available plugin 1', author: 'Author 1' },
        { name: 'available-plugin2', version: '1.5.0', description: 'Available plugin 2' }
      ]);

      const result = await mcpCommand.handler(['plugins', 'discover'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Discovered Plugins');
      expect(result.message).toContain('available-plugin1');
      expect(result.message).toContain('available-plugin2');
      expect(result.message).toContain('Author 1');
    });

    test('should enable plugin successfully', async () => {
      mockPluginManager.enablePlugin.mockResolvedValue(true);

      const result = await mcpCommand.handler(['plugins', 'enable', 'test-plugin'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('Plugin \'test-plugin\' enabled successfully');
      expect(mockPluginManager.enablePlugin).toHaveBeenCalledWith('test-plugin');
    });

    test('should handle enable plugin failure', async () => {
      mockPluginManager.enablePlugin.mockResolvedValue(false);

      const result = await mcpCommand.handler(['plugins', 'enable', 'non-existent'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Failed to enable plugin \'non-existent\'');
    });

    test('should disable plugin successfully', async () => {
      mockPluginManager.disablePlugin.mockResolvedValue(true);

      const result = await mcpCommand.handler(['plugins', 'disable', 'test-plugin'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('Plugin \'test-plugin\' disabled successfully');
      expect(mockPluginManager.disablePlugin).toHaveBeenCalledWith('test-plugin');
    });

    test('should unload plugin successfully', async () => {
      mockPluginManager.unloadPlugin.mockResolvedValue(true);

      const result = await mcpCommand.handler(['plugins', 'unload', 'test-plugin'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('Plugin \'test-plugin\' unloaded successfully');
      expect(mockPluginManager.unloadPlugin).toHaveBeenCalledWith('test-plugin');
    });

    test('should create plugin template', async () => {
      const result = await mcpCommand.handler(['plugins', 'create', 'new-plugin'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Plugin template \'new-plugin\' created successfully');
      expect(mockPluginManager.createPluginTemplate).toHaveBeenCalledWith('new-plugin', testContext.projectRoot);
    });

    test('should handle missing plugin name for operations', async () => {
      const result = await mcpCommand.handler(['plugins', 'enable'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toBe('Please specify plugin name');
    });
  });

  describe('Capabilities Management', () => {
    beforeEach(async () => {
      await mcpCommand.handler(['start'], testContext);
    });

    test('should list server capabilities', async () => {
      const result = await mcpCommand.handler(['capabilities'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Server Capabilities');
      expect(result.message).toContain('health-check');
      expect(result.message).toContain('metrics');
      expect(result.message).toContain('✅ Enabled');
      expect(result.capabilities).toBeDefined();
    });

    test('should enable capability', async () => {
      const result = await mcpCommand.handler(['capabilities', 'enable', 'test-capability'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('Capability \'test-capability\' enabled successfully');
      expect(mockServer.setCapability).toHaveBeenCalledWith('test-capability', true);
    });

    test('should disable capability', async () => {
      const result = await mcpCommand.handler(['capabilities', 'disable', 'test-capability'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('Capability \'test-capability\' disabled successfully');
      expect(mockServer.setCapability).toHaveBeenCalledWith('test-capability', false);
    });

    test('should handle missing capability name', async () => {
      const result = await mcpCommand.handler(['capabilities', 'enable'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toBe('Please specify capability name');
    });
  });

  describe('Metrics', () => {
    beforeEach(async () => {
      await mcpCommand.handler(['start'], testContext);
    });

    test('should display server metrics', async () => {
      const result = await mcpCommand.handler(['metrics'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('MCP Server Metrics');
      expect(result.message).toContain('Total Requests: 100');
      expect(result.message).toContain('Error Count: 5');
      expect(result.message).toContain('Success Rate: 95%');
      expect(result.message).toContain('Average Response Time: 50ms');
      expect(result.metrics).toBeDefined();
    });

    test('should handle metrics when server not running', async () => {
      await mcpCommand.handler(['stop'], testContext);

      const result = await mcpCommand.handler(['metrics'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toBe('MCP Server is not running');
    });
  });

  describe('Configuration Management', () => {
    test('should show existing configuration', async () => {
      vi.mocked(fs.readFile).mockResolvedValue(JSON.stringify({
        name: 'configured-server',
        version: '2.0.0',
        description: 'Configured server',
        endpoints: [{}],
        middleware: [{}],
        plugins: [{}],
        capabilities: [{}]
      }));

      const result = await mcpCommand.handler(['config', 'show'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('MCP Server Configuration');
      expect(result.message).toContain('configured-server');
      expect(result.message).toContain('Endpoints: 1');
    });

    test('should handle missing configuration', async () => {
      vi.mocked(fs.readFile).mockRejectedValue(new Error('File not found'));

      const result = await mcpCommand.handler(['config', 'show'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toBe('No MCP server configuration found');
    });

    test('should create default configuration', async () => {
      const result = await mcpCommand.handler(['config', 'create'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('Default MCP server configuration created');
      expect(vi.mocked(fs.writeFile)).toHaveBeenCalled();
    });
  });

  describe('Help Command', () => {
    test('should display help information', async () => {
      const result = await mcpCommand.handler(['help'], testContext);

      expect(result.success).toBe(true);
      expect(result.message).toContain('MCP Command Help');
      expect(result.message).toContain('/ae:mcp <action>');
      expect(result.message).toContain('start');
      expect(result.message).toContain('plugins');
      expect(result.message).toContain('capabilities');
    });
  });

  describe('Error Handling', () => {
    test('should handle missing action', async () => {
      const result = await mcpCommand.handler([], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('No action specified');
    });

    test('should handle unknown action', async () => {
      const result = await mcpCommand.handler(['unknown'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Unknown action: unknown');
    });

    test('should handle server start errors', async () => {
      mockPluginManager.loadPluginsFromDirectory.mockResolvedValue([]);
      mockServer.start.mockRejectedValue(new Error('Server start failed'));

      const result = await mcpCommand.handler(['start'], testContext);

      expect(result.success).toBe(false);
      expect(result.message).toContain('Failed to start MCP server');
      expect(result.message).toContain('Server start failed');
    });
  });
});