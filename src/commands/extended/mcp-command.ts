/**
 * MCP Command for ae-framework
 * Manages MCP server instances, plugins, and extensions
 */

import { BaseExtendedCommand, ExtendedCommandResult, ExtendedCommandConfig } from './base-command.js';
import { MCPServer, MCPServerConfig } from '../../services/mcp-server.js';
import { MCPPluginManager } from '../../utils/mcp-plugin-manager.js';
import { ContextManager } from '../../utils/context-manager.js';
import { TokenOptimizer } from '../../utils/token-optimizer.js';
import * as fs from 'fs/promises';
import * as path from 'path';

export interface MCPCommandResult extends ExtendedCommandResult {
  serverStatus?: any;
  pluginList?: string[];
  capabilities?: any[];
  metrics?: any;
  pluginDetails?: any;
  recommendations?: string[];
}

export class MCPCommand extends BaseExtendedCommand {
  public readonly name = '/ae:mcp';
  public readonly description = 'Manage MCP server, plugins, and extensions';
  public readonly category = 'utility' as const;
  public readonly usage = '/ae:mcp <action> [options]';
  public readonly aliases = ['/mcp', '/server', '/a:mcp'];

  private mcpServer?: MCPServer;
  private pluginManager?: MCPPluginManager;
  private contextManager?: ContextManager;
  private tokenOptimizer?: TokenOptimizer;

  constructor(config?: ExtendedCommandConfig) {
    super(config);
  }

  private async getMCPServer(projectRoot: string): Promise<MCPServer> {
    if (!this.mcpServer) {
      const serverConfig = await this.loadServerConfig(projectRoot);
      this.mcpServer = new MCPServer(serverConfig, projectRoot);
    }
    return this.mcpServer;
  }

  private getPluginManager(projectRoot: string): MCPPluginManager {
    if (!this.pluginManager) {
      this.pluginManager = new MCPPluginManager(projectRoot);
    }
    return this.pluginManager;
  }

  private async getContextManager(projectRoot: string): Promise<ContextManager> {
    if (!this.contextManager) {
      this.contextManager = new ContextManager(projectRoot);
    }
    return this.contextManager;
  }

  private getTokenOptimizer(): TokenOptimizer {
    if (!this.tokenOptimizer) {
      this.tokenOptimizer = new TokenOptimizer();
    }
    return this.tokenOptimizer;
  }

  async handler(args: string[], context: any): Promise<MCPCommandResult> {
    const startTime = Date.now();
    const projectRoot = context?.projectRoot || process.cwd();

    try {
      const action = args[0]?.toLowerCase();

      if (!action) {
        return this.createErrorResult('No action specified. Use: start, stop, status, plugins, capabilities');
      }

      switch (action) {
        case 'start':
          return await this.handleStartServer(projectRoot);

        case 'stop':
          return await this.handleStopServer();

        case 'restart':
          return await this.handleRestartServer(projectRoot);

        case 'status':
          return await this.handleServerStatus();

        case 'plugins':
          return await this.handlePluginManagement(args.slice(1), projectRoot);

        case 'capabilities':
          return await this.handleCapabilities(args.slice(1));

        case 'metrics':
          return await this.handleMetrics();

        case 'config':
          return await this.handleConfigManagement(args.slice(1), projectRoot);

        case 'help':
          return this.handleHelp();

        default:
          return this.createErrorResult(`Unknown action: ${action}. Use /ae:mcp help for available actions`);
      }

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`MCP command failed: ${error.message}`);
    } finally {
      this.recordMetric('execution_time', Date.now() - startTime);
    }
  }

  private async handleStartServer(projectRoot: string): Promise<MCPCommandResult> {
    try {
      const server = await this.getMCPServer(projectRoot);
      const pluginManager = this.getPluginManager(projectRoot);
      
      // Set up plugin manager with server
      pluginManager.setServer(server);

      // Load plugins
      const pluginResults = await pluginManager.loadPluginsFromDirectory(
        path.join(projectRoot, 'plugins')
      );

      const loadedPlugins = pluginResults.filter(r => r.success).length;
      const failedPlugins = pluginResults.filter(r => !r.success);

      // Start server
      await server.start();

      let message = `MCP Server started successfully!\n\n`;
      message += `Loaded ${loadedPlugins} plugins\n`;
      
      if (failedPlugins.length > 0) {
        message += `Failed to load ${failedPlugins.length} plugins:\n`;
        failedPlugins.forEach(p => {
          message += `  • ${p.error}\n`;
        });
        message += '\n';
      }

      const status = server.getStatus();
      message += `Server: ${status.config.name}\n`;
      message += `Version: ${status.config.version}\n`;
      message += `Running: ${status.running}`;

      this.recordMetric('success');
      this.recordMetric('server_started');

      return {
        success: true,
        message,
        serverStatus: status,
        evidence: [`Server started with ${loadedPlugins} plugins`],
        recommendations: ['Use /ae:mcp status to monitor server health']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to start MCP server: ${error.message}`);
    }
  }

  private async handleStopServer(): Promise<MCPCommandResult> {
    try {
      if (!this.mcpServer) {
        return this.createErrorResult('No MCP server instance found');
      }

      await this.mcpServer.stop();
      this.mcpServer = undefined;

      this.recordMetric('success');
      this.recordMetric('server_stopped');

      return {
        success: true,
        message: 'MCP Server stopped successfully',
        evidence: ['Server gracefully shut down'],
        recommendations: ['Use /ae:mcp start to restart the server']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to stop MCP server: ${error.message}`);
    }
  }

  private async handleRestartServer(projectRoot: string): Promise<MCPCommandResult> {
    try {
      // Stop server if running
      if (this.mcpServer) {
        await this.mcpServer.stop();
        this.mcpServer = undefined;
      }

      // Start server again
      const startResult = await this.handleStartServer(projectRoot);
      
      if (startResult.success) {
        startResult.message = 'MCP Server restarted successfully!\n\n' + startResult.message;
      }

      return startResult;

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to restart MCP server: ${error.message}`);
    }
  }

  private async handleServerStatus(): Promise<MCPCommandResult> {
    try {
      if (!this.mcpServer) {
        return {
          success: true,
          message: 'MCP Server is not running',
          serverStatus: { running: false },
          evidence: ['No active server instance'],
          recommendations: ['Use /ae:mcp start to start the server']
        };
      }

      const status = this.mcpServer.getStatus();
      const metrics = this.mcpServer.getMetrics();

      let message = `MCP Server Status:\n\n`;
      message += `Name: ${status.config.name}\n`;
      message += `Version: ${status.config.version}\n`;
      message += `Running: ${status.running}\n`;
      message += `Uptime: ${Math.round(status.uptime / 1000)}s\n\n`;

      message += `Metrics:\n`;
      message += `  Requests: ${metrics.requestCount}\n`;
      message += `  Errors: ${metrics.errorCount}\n`;
      message += `  Avg Response Time: ${metrics.averageResponseTime}ms\n`;
      message += `  Plugins Loaded: ${metrics.pluginsLoaded}\n`;
      message += `  Endpoints: ${metrics.endpointsRegistered}`;

      this.recordMetric('success');

      return {
        success: true,
        message,
        serverStatus: status,
        metrics,
        evidence: [`Server uptime: ${Math.round(status.uptime / 1000)}s`],
        recommendations: status.running ? 
          ['Monitor metrics regularly for performance insights'] :
          ['Use /ae:mcp start to start the server']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to get server status: ${error.message}`);
    }
  }

  private async handlePluginManagement(args: string[], projectRoot: string): Promise<MCPCommandResult> {
    const pluginAction = args[0]?.toLowerCase();

    switch (pluginAction) {
      case 'list':
        return await this.handleListPlugins(projectRoot);

      case 'load':
        return await this.handleLoadPlugin(args[1], projectRoot);

      case 'enable':
        return await this.handleEnablePlugin(args[1], projectRoot);

      case 'disable':
        return await this.handleDisablePlugin(args[1], projectRoot);

      case 'unload':
        return await this.handleUnloadPlugin(args[1], projectRoot);

      case 'create':
        return await this.handleCreatePlugin(args[1], args[2] || projectRoot, projectRoot);

      case 'discover':
        return await this.handleDiscoverPlugins(projectRoot);

      default:
        return await this.handleListPlugins(projectRoot);
    }
  }

  private async handleListPlugins(projectRoot: string): Promise<MCPCommandResult> {
    try {
      const pluginManager = this.getPluginManager(projectRoot);
      const plugins = pluginManager.getLoadedPlugins();

      let message = 'Loaded Plugins:\n\n';
      
      if (plugins.length === 0) {
        message += 'No plugins loaded\n\n';
        message += 'Use /ae:mcp plugins discover to find available plugins';
      } else {
        plugins.forEach(plugin => {
          const status = plugin.enabled ? '✅' : '❌';
          message += `${status} ${plugin.manifest.name} v${plugin.manifest.version}\n`;
          message += `    ${plugin.manifest.description || 'No description'}\n`;
          message += `    Loaded: ${new Date(plugin.loadedAt).toLocaleString()}\n\n`;
        });
      }

      this.recordMetric('success');

      return {
        success: true,
        message,
        pluginList: plugins.map(p => p.manifest.name),
        evidence: [`Found ${plugins.length} loaded plugins`],
        recommendations: plugins.length === 0 ? 
          ['Use /ae:mcp plugins discover to find plugins'] : 
          ['Use /ae:mcp plugins <name> for plugin details']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to list plugins: ${error.message}`);
    }
  }

  private async handleCapabilities(args: string[]): Promise<MCPCommandResult> {
    try {
      if (!this.mcpServer) {
        return this.createErrorResult('MCP Server is not running');
      }

      const capabilities = this.mcpServer.getCapabilities();
      const action = args[0]?.toLowerCase();

      if (action === 'enable' || action === 'disable') {
        const capabilityName = args[1];
        if (!capabilityName) {
          return this.createErrorResult(`Please specify capability name`);
        }

        this.mcpServer.setCapability(capabilityName, action === 'enable');
        
        return {
          success: true,
          message: `Capability '${capabilityName}' ${action}d successfully`,
          evidence: [`Capability ${capabilityName} is now ${action}d`],
          recommendations: ['Use /ae:mcp capabilities to see all capabilities']
        };
      }

      let message = 'Server Capabilities:\n\n';
      capabilities.forEach(cap => {
        const status = cap.enabled ? '✅ Enabled' : '❌ Disabled';
        message += `${cap.name} v${cap.version} - ${status}\n`;
        message += `  ${cap.description || 'No description'}\n\n`;
      });

      this.recordMetric('success');

      return {
        success: true,
        message,
        capabilities,
        evidence: [`Found ${capabilities.length} capabilities`],
        recommendations: ['Use /ae:mcp capabilities enable/disable <name> to modify']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to manage capabilities: ${error.message}`);
    }
  }

  private async handleMetrics(): Promise<MCPCommandResult> {
    try {
      if (!this.mcpServer) {
        return this.createErrorResult('MCP Server is not running');
      }

      const metrics = this.mcpServer.getMetrics();

      let message = 'MCP Server Metrics:\n\n';
      message += `Total Requests: ${metrics.requestCount}\n`;
      message += `Error Count: ${metrics.errorCount}\n`;
      message += `Success Rate: ${metrics.requestCount > 0 ? 
        Math.round(((metrics.requestCount - metrics.errorCount) / metrics.requestCount) * 100) : 0}%\n`;
      message += `Average Response Time: ${metrics.averageResponseTime}ms\n`;
      message += `Uptime: ${Math.round(metrics.uptime / 1000)}s\n`;
      message += `Active Connections: ${metrics.activeConnections}\n`;
      message += `Plugins Loaded: ${metrics.pluginsLoaded}\n`;
      message += `Endpoints Registered: ${metrics.endpointsRegistered}`;

      this.recordMetric('success');

      return {
        success: true,
        message,
        metrics,
        evidence: [`Server processed ${metrics.requestCount} requests`],
        recommendations: ['Monitor error rate and response times for performance']
      };

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to get metrics: ${error.message}`);
    }
  }

  private async handleConfigManagement(args: string[], projectRoot: string): Promise<MCPCommandResult> {
    const configAction = args[0]?.toLowerCase();

    switch (configAction) {
      case 'show':
        return await this.handleShowConfig(projectRoot);

      case 'create':
        return await this.handleCreateConfig(projectRoot);

      default:
        return await this.handleShowConfig(projectRoot);
    }
  }

  private async handleShowConfig(projectRoot: string): Promise<MCPCommandResult> {
    try {
      const configPath = path.join(projectRoot, '.ae-framework', 'mcp-server.json');
      
      try {
        const configContent = await fs.readFile(configPath, 'utf-8');
        const config = JSON.parse(configContent);

        let message = 'MCP Server Configuration:\n\n';
        message += `Name: ${config.name}\n`;
        message += `Version: ${config.version}\n`;
        message += `Description: ${config.description || 'None'}\n`;
        message += `Endpoints: ${config.endpoints?.length || 0}\n`;
        message += `Middleware: ${config.middleware?.length || 0}\n`;
        message += `Plugins: ${config.plugins?.length || 0}\n`;
        message += `Capabilities: ${config.capabilities?.length || 0}`;

        return {
          success: true,
          message,
          evidence: [`Configuration loaded from ${configPath}`],
          recommendations: ['Use /ae:mcp config create to generate default config']
        };

      } catch (error) {
        return {
          success: true,
          message: 'No MCP server configuration found',
          evidence: ['Configuration file does not exist'],
          recommendations: ['Use /ae:mcp config create to generate default config']
        };
      }

    } catch (error: any) {
      this.recordMetric('error');
      return this.createErrorResult(`Failed to show config: ${error.message}`);
    }
  }

  private handleHelp(): MCPCommandResult {
    const helpMessage = `MCP Command Help

Usage: /ae:mcp <action> [options]

Server Actions:
  • start              Start the MCP server
  • stop               Stop the MCP server
  • restart            Restart the MCP server
  • status             Show server status and metrics
  • metrics            Show detailed metrics

Plugin Actions:
  • plugins list       List all loaded plugins
  • plugins load <dir> Load plugins from directory
  • plugins enable <name>   Enable a plugin
  • plugins disable <name>  Disable a plugin
  • plugins create <name>   Create a new plugin template
  • plugins discover   Discover available plugins

Capability Actions:
  • capabilities       List all server capabilities
  • capabilities enable <name>   Enable a capability
  • capabilities disable <name>  Disable a capability

Configuration Actions:
  • config show        Show current configuration
  • config create      Create default configuration

Examples:
  /ae:mcp start                    # Start MCP server
  /ae:mcp plugins list             # List loaded plugins
  /ae:mcp capabilities             # Show server capabilities
  /ae:mcp metrics                  # View performance metrics`;

    this.recordMetric('help_requested');
    return {
      success: true,
      message: helpMessage,
      evidence: ['Help information provided'],
      recommendations: ['Use /ae:mcp start to begin using MCP server']
    };
  }

  private async loadServerConfig(projectRoot: string): Promise<MCPServerConfig> {
    const configPath = path.join(projectRoot, '.ae-framework', 'mcp-server.json');
    
    try {
      const configContent = await fs.readFile(configPath, 'utf-8');
      return JSON.parse(configContent);
    } catch (error) {
      // Return default configuration
      return {
        name: 'ae-framework-server',
        version: '1.0.0',
        description: 'AE Framework MCP Server',
        endpoints: [],
        capabilities: [
          { name: 'health-check', version: '1.0.0', enabled: true },
          { name: 'metrics', version: '1.0.0', enabled: true }
        ]
      };
    }
  }

  private async handleDiscoverPlugins(projectRoot: string): Promise<MCPCommandResult> {
    try {
      const pluginManager = this.getPluginManager(projectRoot);
      const discovered = await pluginManager.discoverPlugins();

      let message = 'Discovered Plugins:\n\n';
      
      if (discovered.length === 0) {
        message += 'No plugins found in search paths';
      } else {
        discovered.forEach(plugin => {
          message += `• ${plugin.name} v${plugin.version}\n`;
          message += `  ${plugin.description || 'No description'}\n`;
          message += `  Author: ${plugin.author || 'Unknown'}\n\n`;
        });
      }

      return {
        success: true,
        message,
        evidence: [`Discovered ${discovered.length} plugins`],
        recommendations: discovered.length > 0 ? 
          ['Use /ae:mcp plugins load to load specific plugins'] : 
          ['Create plugins using /ae:mcp plugins create <name>']
      };

    } catch (error: any) {
      return this.createErrorResult(`Failed to discover plugins: ${error.message}`);
    }
  }

  private async handleLoadPlugin(pluginPath: string, projectRoot: string): Promise<MCPCommandResult> {
    if (!pluginPath) {
      return this.createErrorResult('Please specify plugin path or directory');
    }

    try {
      const pluginManager = this.getPluginManager(projectRoot);
      const results = await pluginManager.loadPluginsFromDirectory(pluginPath);
      
      const successful = results.filter(r => r.success);
      const failed = results.filter(r => !r.success);

      let message = `Plugin Loading Results:\n\n`;
      message += `Successfully loaded: ${successful.length}\n`;
      message += `Failed to load: ${failed.length}\n`;

      if (failed.length > 0) {
        message += '\nErrors:\n';
        failed.forEach(f => message += `  • ${f.error}\n`);
      }

      return {
        success: successful.length > 0,
        message,
        evidence: [`Loaded ${successful.length} plugins`],
        recommendations: ['Use /ae:mcp plugins list to see loaded plugins']
      };

    } catch (error: any) {
      return this.createErrorResult(`Failed to load plugins: ${error.message}`);
    }
  }

  private async handleEnablePlugin(pluginName: string, projectRoot: string): Promise<MCPCommandResult> {
    if (!pluginName) {
      return this.createErrorResult('Please specify plugin name');
    }

    try {
      const pluginManager = this.getPluginManager(projectRoot);
      const success = await pluginManager.enablePlugin(pluginName);

      if (success) {
        return {
          success: true,
          message: `Plugin '${pluginName}' enabled successfully`,
          evidence: [`Plugin ${pluginName} is now active`],
          recommendations: ['Check plugin functionality with appropriate endpoints']
        };
      } else {
        return this.createErrorResult(`Failed to enable plugin '${pluginName}' - plugin not found`);
      }

    } catch (error: any) {
      return this.createErrorResult(`Failed to enable plugin: ${error.message}`);
    }
  }

  private async handleDisablePlugin(pluginName: string, projectRoot: string): Promise<MCPCommandResult> {
    if (!pluginName) {
      return this.createErrorResult('Please specify plugin name');
    }

    try {
      const pluginManager = this.getPluginManager(projectRoot);
      const success = await pluginManager.disablePlugin(pluginName);

      if (success) {
        return {
          success: true,
          message: `Plugin '${pluginName}' disabled successfully`,
          evidence: [`Plugin ${pluginName} is now inactive`],
          recommendations: ['Use /ae:mcp plugins enable to re-enable when needed']
        };
      } else {
        return this.createErrorResult(`Failed to disable plugin '${pluginName}' - plugin not found`);
      }

    } catch (error: any) {
      return this.createErrorResult(`Failed to disable plugin: ${error.message}`);
    }
  }

  private async handleUnloadPlugin(pluginName: string, projectRoot: string): Promise<MCPCommandResult> {
    if (!pluginName) {
      return this.createErrorResult('Please specify plugin name');
    }

    try {
      const pluginManager = this.getPluginManager(projectRoot);
      const success = await pluginManager.unloadPlugin(pluginName);

      if (success) {
        return {
          success: true,
          message: `Plugin '${pluginName}' unloaded successfully`,
          evidence: [`Plugin ${pluginName} removed from memory`],
          recommendations: ['Plugin can be reloaded using /ae:mcp plugins load']
        };
      } else {
        return this.createErrorResult(`Failed to unload plugin '${pluginName}' - plugin not found`);
      }

    } catch (error: any) {
      return this.createErrorResult(`Failed to unload plugin: ${error.message}`);
    }
  }

  private async handleCreatePlugin(pluginName: string, targetDir: string, projectRoot: string): Promise<MCPCommandResult> {
    if (!pluginName) {
      return this.createErrorResult('Please specify plugin name');
    }

    try {
      const pluginManager = this.getPluginManager(projectRoot);
      await pluginManager.createPluginTemplate(pluginName, targetDir);

      const pluginPath = path.join(targetDir, pluginName);

      return {
        success: true,
        message: `Plugin template '${pluginName}' created successfully at ${pluginPath}`,
        evidence: [`Created plugin template with manifest and implementation`],
        recommendations: [
          'Edit the plugin implementation in index.js',
          'Load the plugin using /ae:mcp plugins load'
        ]
      };

    } catch (error: any) {
      return this.createErrorResult(`Failed to create plugin template: ${error.message}`);
    }
  }

  private async handleCreateConfig(projectRoot: string): Promise<MCPCommandResult> {
    try {
      const configDir = path.join(projectRoot, '.ae-framework');
      const configPath = path.join(configDir, 'mcp-server.json');

      // Create directory if it doesn't exist
      await fs.mkdir(configDir, { recursive: true });

      // Default configuration
      const defaultConfig: MCPServerConfig = {
        name: 'ae-framework-server',
        version: '1.0.0',
        description: 'AE Framework MCP Server',
        endpoints: [],
        capabilities: [
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
            description: 'Dynamic plugin loading',
            enabled: true
          }
        ]
      };

      await fs.writeFile(configPath, JSON.stringify(defaultConfig, null, 2));

      return {
        success: true,
        message: `Default MCP server configuration created at ${configPath}`,
        evidence: ['Configuration file created with default settings'],
        recommendations: ['Customize the configuration as needed for your project']
      };

    } catch (error: any) {
      return this.createErrorResult(`Failed to create config: ${error.message}`);
    }
  }

  private createErrorResult(message: string): MCPCommandResult {
    return {
      success: false,
      message,
      evidence: ['Command execution failed'],
      recommendations: ['Use /ae:mcp help for usage information']
    };
  }

  // Required abstract method implementations
  protected validateArgs(args: string[]): { isValid: boolean; message?: string } {
    if (args.length === 0) {
      return {
        isValid: false,
        message: 'Please specify an action: start, stop, status, install, list, or help'
      };
    }
    return { isValid: true };
  }

  protected async execute(
    args: string[], 
    options: Record<string, any>, 
    context: any
  ): Promise<ExtendedCommandResult> {
    return await this.handler(args, context);
  }

  protected generateValidationClaim(data: any): string {
    if (data.serverStatus) {
      return `MCP server status is: ${data.serverStatus}`;
    } else if (data.installedPlugin) {
      return `MCP plugin "${data.installedPlugin}" was successfully installed`;
    }
    return 'MCP operation was completed';
  }

  protected generateSummary(data: any): string {
    if (data.serverStatus) {
      return `MCP server is ${data.serverStatus}`;
    } else if (data.installedPlugin) {
      return `Successfully installed MCP plugin: ${data.installedPlugin}`;
    }
    return 'MCP operation completed';
  }
}