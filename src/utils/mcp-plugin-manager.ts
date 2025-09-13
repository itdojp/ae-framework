/**
 * MCP Plugin Manager for ae-framework
 * Manages loading, registration, and lifecycle of MCP plugins
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import type { MCPPlugin, MCPServer } from '../services/mcp-server.js';

export interface PluginManifest {
  name: string;
  version: string;
  description?: string;
  main: string;
  dependencies?: string[];
  mcpDependencies?: string[];
  author?: string;
  license?: string;
  keywords?: string[];
  repository?: string;
  homepage?: string;
  engines?: {
    node?: string;
    'ae-framework'?: string;
  };
}

export interface PluginRegistration {
  manifest: PluginManifest;
  plugin: MCPPlugin;
  filePath: string;
  loadedAt: number;
  enabled: boolean;
}

export interface PluginLoadResult {
  success: boolean;
  plugin?: PluginRegistration;
  error?: string;
  warnings?: string[];
}

export interface PluginDiscoveryOptions {
  searchPaths: string[];
  includeDevPlugins: boolean;
  skipValidation: boolean;
}

export class MCPPluginManager {
  private plugins: Map<string, PluginRegistration> = new Map();
  private pluginPaths: string[] = [];
  private projectRoot: string;
  private server?: MCPServer;

  constructor(projectRoot: string, pluginPaths: string[] = []) {
    this.projectRoot = projectRoot;
    this.pluginPaths = [
      ...pluginPaths,
      path.join(projectRoot, 'plugins'),
      path.join(projectRoot, '.ae-framework', 'plugins'),
      path.join(projectRoot, 'node_modules', '@ae-framework'),
      path.join(__dirname, '..', '..', 'plugins')
    ];
  }

  /**
   * Set the MCP server instance for plugin registration
   */
  setServer(server: MCPServer): void {
    this.server = server;
  }

  /**
   * Discover all available plugins
   */
  async discoverPlugins(options: Partial<PluginDiscoveryOptions> = {}): Promise<PluginManifest[]> {
    const searchOptions: PluginDiscoveryOptions = {
      searchPaths: this.pluginPaths,
      includeDevPlugins: false,
      skipValidation: false,
      ...options
    };

    const discovered: PluginManifest[] = [];

    for (const searchPath of searchOptions.searchPaths) {
      try {
        const plugins = await this.scanPluginDirectory(searchPath, searchOptions);
        discovered.push(...plugins);
      } catch (error) {
        // Skip directories that don't exist or can't be read
        continue;
      }
    }

    return discovered;
  }

  /**
   * Load a plugin from its manifest
   */
  async loadPlugin(manifest: PluginManifest, filePath: string): Promise<PluginLoadResult> {
    try {
      // Check if plugin is already loaded
      if (this.plugins.has(manifest.name)) {
        return {
          success: false,
          error: `Plugin ${manifest.name} is already loaded`
        };
      }

      // Validate plugin manifest
      const validationError = this.validateManifest(manifest);
      if (validationError) {
        return {
          success: false,
          error: `Invalid plugin manifest: ${validationError}`
        };
      }

      // Load plugin module
      const pluginModulePath = path.join(path.dirname(filePath), manifest.main);
      const pluginModule = await this.loadPluginModule(pluginModulePath);

      if (!pluginModule || typeof pluginModule.initialize !== 'function') {
        return {
          success: false,
          error: `Plugin ${manifest.name} does not export a valid initialize function`
        };
      }

      // Create plugin registration
      const plugin: MCPPlugin = {
        name: manifest.name,
        version: manifest.version,
        initialize: pluginModule.initialize,
        ...(pluginModule.terminate ? { terminate: pluginModule.terminate } : {}),
        ...(manifest.description ? { description: manifest.description } : {}),
        ...(manifest.mcpDependencies ? { dependencies: manifest.mcpDependencies } : {}),
        ...(pluginModule.endpoints ? { endpoints: pluginModule.endpoints } : {}),
        ...(pluginModule.middleware ? { middleware: pluginModule.middleware } : {})
      };

      const registration: PluginRegistration = {
        manifest,
        plugin,
        filePath,
        loadedAt: Date.now(),
        enabled: true
      };

      this.plugins.set(manifest.name, registration);

      // Register with MCP server if available
      if (this.server) {
        await this.server.registerPlugin(plugin);
      }

      return {
        success: true,
        plugin: registration
      };

    } catch (error: any) {
      return {
        success: false,
        error: `Failed to load plugin: ${error.message}`
      };
    }
  }

  /**
   * Load plugins from directory
   */
  async loadPluginsFromDirectory(directoryPath: string): Promise<PluginLoadResult[]> {
    const results: PluginLoadResult[] = [];

    try {
      const plugins = await this.scanPluginDirectory(directoryPath, {
        searchPaths: [directoryPath],
        includeDevPlugins: true,
        skipValidation: false
      });

      for (const manifest of plugins) {
        const manifestPath = path.join(directoryPath, manifest.name, 'plugin.json');
        const result = await this.loadPlugin(manifest, manifestPath);
        results.push(result);
      }

    } catch (error: any) {
      results.push({
        success: false,
        error: `Failed to load plugins from directory: ${error.message}`
      });
    }

    return results;
  }

  /**
   * Enable a plugin
   */
  async enablePlugin(name: string): Promise<boolean> {
    const registration = this.plugins.get(name);
    if (!registration) {
      return false;
    }

    if (registration.enabled) {
      return true;
    }

    // Register with MCP server if available
    if (this.server) {
      try {
        await this.server.registerPlugin(registration.plugin);
        registration.enabled = true;
        return true;
      } catch (error) {
        return false;
      }
    }

    registration.enabled = true;
    return true;
  }

  /**
   * Disable a plugin
   */
  async disablePlugin(name: string): Promise<boolean> {
    const registration = this.plugins.get(name);
    if (!registration) {
      return false;
    }

    if (!registration.enabled) {
      return true;
    }

    // Terminate plugin if it has a terminate function
    if (registration.plugin.terminate && this.server) {
      try {
        await registration.plugin.terminate(this.server);
      } catch (error) {
        // Log error but continue with disabling
      }
    }

    registration.enabled = false;
    return true;
  }

  /**
   * Unload a plugin
   */
  async unloadPlugin(name: string): Promise<boolean> {
    const registration = this.plugins.get(name);
    if (!registration) {
      return false;
    }

    // Disable plugin first
    await this.disablePlugin(name);

    // Remove from registry
    this.plugins.delete(name);
    return true;
  }

  /**
   * Get all loaded plugins
   */
  getLoadedPlugins(): PluginRegistration[] {
    return Array.from(this.plugins.values());
  }

  /**
   * Get plugin by name
   */
  getPlugin(name: string): PluginRegistration | undefined {
    return this.plugins.get(name);
  }

  /**
   * Get enabled plugins
   */
  getEnabledPlugins(): PluginRegistration[] {
    return Array.from(this.plugins.values()).filter(p => p.enabled);
  }

  /**
   * Create a new plugin template
   */
  async createPluginTemplate(name: string, targetDir: string): Promise<void> {
    const pluginDir = path.join(targetDir, name);
    await fs.mkdir(pluginDir, { recursive: true });

    // Create plugin manifest
    const manifest: PluginManifest = {
      name,
      version: '1.0.0',
      description: `${name} plugin for ae-framework`,
      main: 'index.js',
      author: 'Generated',
      license: 'MIT',
      engines: {
        node: '>=18.0.0',
        'ae-framework': '>=1.0.0'
      }
    };

    await fs.writeFile(
      path.join(pluginDir, 'plugin.json'),
      JSON.stringify(manifest, null, 2)
    );

    // Create plugin implementation
    const pluginCode = `/**
 * ${name} Plugin for ae-framework
 */

/**
 * Initialize plugin
 */
async function initialize(server) {
  console.log('${name} plugin initialized');
  
  // Register plugin endpoints
  server.registerEndpoint({
    path: '/${name}/hello',
    method: 'GET',
    handler: async (request) => ({
      status: 200,
      data: { message: 'Hello from ${name} plugin!' }
    }),
    description: 'Test endpoint for ${name} plugin'
  });
}

/**
 * Terminate plugin
 */
async function terminate(server) {
  console.log('${name} plugin terminated');
}

module.exports = {
  initialize,
  terminate
};
`;

    await fs.writeFile(path.join(pluginDir, 'index.js'), pluginCode);

    // Create README
    const readme = `# ${name} Plugin

${manifest.description}

## Installation

Copy this plugin to your ae-framework plugins directory.

## Usage

This plugin provides the following endpoints:

- \`GET /${name}/hello\` - Test endpoint

## Configuration

No additional configuration required.
`;

    await fs.writeFile(path.join(pluginDir, 'README.md'), readme);
  }

  // Private methods

  private async scanPluginDirectory(
    directoryPath: string, 
    options: PluginDiscoveryOptions
  ): Promise<PluginManifest[]> {
    const plugins: PluginManifest[] = [];

    try {
      const entries = await fs.readdir(directoryPath, { withFileTypes: true });

      for (const entry of entries) {
        if (entry.isDirectory()) {
          const pluginManifestPath = path.join(directoryPath, entry.name, 'plugin.json');
          
          try {
            const manifestContent = await fs.readFile(pluginManifestPath, 'utf-8');
            const manifest: PluginManifest = JSON.parse(manifestContent);
            
            // Skip development plugins if not requested
            if (!options.includeDevPlugins && manifest.name.includes('dev')) {
              continue;
            }

            plugins.push(manifest);
          } catch (error) {
            // Skip directories without valid plugin.json
            continue;
          }
        }
      }
    } catch (error) {
      // Directory doesn't exist or can't be read
    }

    return plugins;
  }

  private validateManifest(manifest: PluginManifest): string | null {
    if (!manifest.name || typeof manifest.name !== 'string') {
      return 'Plugin name is required and must be a string';
    }

    if (!manifest.version || typeof manifest.version !== 'string') {
      return 'Plugin version is required and must be a string';
    }

    if (!manifest.main || typeof manifest.main !== 'string') {
      return 'Plugin main file is required and must be a string';
    }

    // Validate version format (basic semver check)
    const versionRegex = /^\d+\.\d+\.\d+/;
    if (!versionRegex.test(manifest.version)) {
      return 'Plugin version must follow semantic versioning (x.y.z)';
    }

    return null;
  }

  private async loadPluginModule(modulePath: string): Promise<any> {
    try {
      // Check if file exists
      await fs.access(modulePath);

      const fileExtension = path.extname(modulePath);
      
      switch (fileExtension) {
        case '.js':
        case '.mjs':
          try {
            // Dynamic import for ES modules
            const module = await import(modulePath);
            return module.default || module;
          } catch (importError: any) {
            // Fallback to require for CommonJS modules
            if (fileExtension === '.js') {
              try {
                delete require.cache[require.resolve(modulePath)];
                return require(modulePath);
              } catch (requireError: any) {
                throw new Error(`Failed to load module as ES module or CommonJS: ${importError.message}, ${requireError.message}`);
              }
            }
            throw importError;
          }
          
        case '.ts':
          throw new Error('TypeScript plugins require compilation. Please compile to JavaScript first.');
          
        case '.json':
          throw new Error('JSON files cannot be loaded as plugins. Please use JavaScript files.');
          
        default:
          throw new Error(`Unsupported plugin file format: ${fileExtension}. Supported formats: .js, .mjs`);
      }
    } catch (error: any) {
      if (error.code === 'ENOENT') {
        throw new Error(`Plugin module file not found: ${modulePath}`);
      }
      throw new Error(`Failed to load plugin module: ${error.message}`);
    }
  }
}
