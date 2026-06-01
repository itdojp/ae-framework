/**
 * MCP Plugin Manager for ae-framework
 * Manages loading, registration, and lifecycle of MCP plugins
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { constants as fsConstants } from 'fs';
import { pathToFileURL } from 'url';
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

interface PluginScanEntry {
  manifest: PluginManifest;
  manifestPath: string;
}

const SAFE_PLUGIN_NAME_PATTERN = /^[a-z][a-z0-9_-]*(?:\.[a-z0-9_-]+)*$/;
const SAFE_PLUGIN_TEMPLATE_NAME_PATTERN = /^[a-z][a-z0-9-]{0,63}$/;
const MAX_PLUGIN_NAME_LENGTH = 80;

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

      // Load plugin module only after manifest-controlled paths have been
      // constrained to the scanned plugin directory.
      const pluginModulePath = await this.resolvePluginModulePath(manifest, filePath);
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
      const plugins = await this.scanPluginDirectoryEntries(directoryPath, {
        searchPaths: [directoryPath],
        includeDevPlugins: true,
        skipValidation: true
      });

      for (const plugin of plugins) {
        const result = await this.loadPlugin(plugin.manifest, plugin.manifestPath);
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
    const nameError = this.validatePluginTemplateName(name);
    if (nameError) {
      throw new Error(nameError);
    }

    const safeTargetDir = await this.resolvePluginTemplateTargetDirectory(targetDir);
    const pluginDir = path.resolve(safeTargetDir, name);
    this.assertPathInside(pluginDir, safeTargetDir, 'Plugin template directory escapes the target directory');
    await fs.mkdir(pluginDir, { recursive: true });
    await this.assertRealPathInsideProject(pluginDir, 'Plugin template directory escapes the project root');

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

    await this.writePluginTemplateFile(pluginDir, 'plugin.json', JSON.stringify(manifest, null, 2));

    const initMessage = JSON.stringify(`${name} plugin initialized`);
    const terminateMessage = JSON.stringify(`${name} plugin terminated`);
    const endpointPath = JSON.stringify(`/${encodeURIComponent(name)}/hello`);
    const helloMessage = JSON.stringify(`Hello from ${name} plugin!`);
    const endpointDescription = JSON.stringify(`Test endpoint for ${name} plugin`);

    // Create plugin implementation
    const pluginCode = `/**
 * ${name} Plugin for ae-framework
 */

/**
 * Initialize plugin
 */
async function initialize(server) {
  console.log(${initMessage});
  
  // Register plugin endpoints
  server.registerEndpoint({
    path: ${endpointPath},
    method: 'GET',
    handler: async (request) => ({
      status: 200,
      data: { message: ${helloMessage} }
    }),
    description: ${endpointDescription}
  });
}

/**
 * Terminate plugin
 */
async function terminate(server) {
  console.log(${terminateMessage});
}

module.exports = {
  initialize,
  terminate
};
`;

    await this.writePluginTemplateFile(pluginDir, 'index.js', pluginCode);

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

    await this.writePluginTemplateFile(pluginDir, 'README.md', readme);
  }

  // Private methods

  private async scanPluginDirectory(
    directoryPath: string, 
    options: PluginDiscoveryOptions
  ): Promise<PluginManifest[]> {
    const entries = await this.scanPluginDirectoryEntries(directoryPath, options);
    return entries.map((entry) => entry.manifest);
  }

  private async scanPluginDirectoryEntries(
    directoryPath: string,
    options: PluginDiscoveryOptions
  ): Promise<PluginScanEntry[]> {
    const plugins: PluginScanEntry[] = [];

    try {
      const entries = await fs.readdir(directoryPath, { withFileTypes: true });

      for (const entry of entries) {
        if (entry.isDirectory()) {
          const pluginDirectory = path.join(directoryPath, entry.name);
          const pluginManifestPath = path.join(pluginDirectory, 'plugin.json');
          
          try {
            const manifestContent = await fs.readFile(pluginManifestPath, 'utf-8');
            const manifest: PluginManifest = JSON.parse(manifestContent);
            
            // Skip development plugins if not requested
            if (!options.includeDevPlugins && manifest.name.includes('dev')) {
              continue;
            }

            if (!options.skipValidation && this.validateManifest(manifest)) {
              continue;
            }

            plugins.push({
              manifest,
              manifestPath: pluginManifestPath
            });
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

    const pluginNameError = this.validatePluginManifestName(manifest.name);
    if (pluginNameError) {
      return pluginNameError;
    }

    if (!manifest.version || typeof manifest.version !== 'string') {
      return 'Plugin version is required and must be a string';
    }

    if (!manifest.main || typeof manifest.main !== 'string') {
      return 'Plugin main file is required and must be a string';
    }

    const pluginMainError = this.validatePluginMainPath(manifest.main);
    if (pluginMainError) {
      return pluginMainError;
    }

    // Validate version format (basic semver check)
    const versionRegex = /^\d+\.\d+\.\d+/;
    if (!versionRegex.test(manifest.version)) {
      return 'Plugin version must follow semantic versioning (x.y.z)';
    }

    return null;
  }

  private validatePluginManifestName(name: string): string | null {
    if (name.length > MAX_PLUGIN_NAME_LENGTH) {
      return `Plugin name must be ${MAX_PLUGIN_NAME_LENGTH} characters or fewer`;
    }

    if (this.hasUnsafePathCharacters(name)) {
      return 'Plugin name must not contain path separators, control characters, or NUL bytes';
    }

    if (!SAFE_PLUGIN_NAME_PATTERN.test(name)) {
      return 'Plugin name must be a safe lowercase plugin identifier';
    }

    return null;
  }

  private validatePluginTemplateName(name: string): string | null {
    if (!name || typeof name !== 'string') {
      return 'Plugin template name is required and must be a string';
    }

    if (this.hasUnsafePathCharacters(name)) {
      return 'Plugin template name must not contain path separators, control characters, or NUL bytes';
    }

    if (!SAFE_PLUGIN_TEMPLATE_NAME_PATTERN.test(name)) {
      return 'Plugin template name must be a lowercase slug using only letters, digits, and hyphens';
    }

    return null;
  }

  private validatePluginMainPath(main: string): string | null {
    if (main.length === 0 || main.trim() !== main) {
      return 'Plugin main file must be a non-empty relative path without surrounding whitespace';
    }

    if (this.hasControlOrNullByte(main) || main.includes('\\')) {
      return 'Plugin main file must not contain backslashes, control characters, or NUL bytes';
    }

    if (path.isAbsolute(main) || /^[A-Za-z]:/.test(main) || main.startsWith('//')) {
      return 'Plugin main file must be a relative path';
    }

    const parts = main.split('/');
    if (parts.some((part) => part === '' || part === '.' || part === '..')) {
      return 'Plugin main file must not contain empty, current-directory, or parent-directory segments';
    }

    const extension = path.posix.extname(main);
    if (extension !== '.js' && extension !== '.mjs') {
      return 'Plugin main file must be a JavaScript module ending in .js or .mjs';
    }

    return null;
  }

  private hasUnsafePathCharacters(value: string): boolean {
    return this.hasControlOrNullByte(value) || value.includes('/') || value.includes('\\');
  }

  private hasControlOrNullByte(value: string): boolean {
    for (let index = 0; index < value.length; index += 1) {
      const codePoint = value.charCodeAt(index);
      if (codePoint <= 0x1f || codePoint === 0x7f) {
        return true;
      }
    }

    return false;
  }

  private async resolvePluginModulePath(manifest: PluginManifest, manifestPath: string): Promise<string> {
    const pluginDirectory = path.dirname(manifestPath);
    const candidateModulePath = path.resolve(pluginDirectory, manifest.main);
    this.assertPathInside(candidateModulePath, pluginDirectory, 'Plugin main file escapes the plugin directory');

    let realPluginDirectory: string;
    let realModulePath: string;

    try {
      realPluginDirectory = await fs.realpath(pluginDirectory);
      realModulePath = await fs.realpath(candidateModulePath);
    } catch (error: any) {
      if (error?.code === 'ENOENT') {
        throw new Error(`Plugin module file not found: ${candidateModulePath}`);
      }
      throw error;
    }

    this.assertPathInside(realModulePath, realPluginDirectory, 'Plugin main file resolves outside the plugin directory');
    return realModulePath;
  }

  private async resolvePluginTemplateTargetDirectory(targetDir: string): Promise<string> {
    if (!targetDir || typeof targetDir !== 'string') {
      throw new Error('Plugin template target directory is required and must be a string');
    }

    if (this.hasControlOrNullByte(targetDir) || targetDir.includes('\\') || /^[A-Za-z]:/.test(targetDir)) {
      throw new Error('Plugin template target directory must not contain control characters, NUL bytes, backslashes, or Windows drive prefixes');
    }

    const resolvedProjectRoot = path.resolve(this.projectRoot);
    const realProjectRoot = await fs.realpath(resolvedProjectRoot);
    const resolvedTargetDir = path.isAbsolute(targetDir)
      ? path.resolve(targetDir)
      : path.resolve(resolvedProjectRoot, targetDir);

    this.assertPathInside(resolvedTargetDir, resolvedProjectRoot, 'Plugin template target directory escapes the project root');

    const realNearestAncestor = await this.realpathNearestExistingAncestor(resolvedTargetDir);
    this.assertPathInside(realNearestAncestor, realProjectRoot, 'Plugin template target directory resolves outside the project root');

    return resolvedTargetDir;
  }

  private async resolvePluginTemplateOutputPath(pluginDir: string, fileName: string): Promise<string> {
    const candidatePath = path.resolve(pluginDir, fileName);
    this.assertPathInside(candidatePath, pluginDir, 'Plugin template output file escapes the plugin directory');

    const realPluginDir = await fs.realpath(pluginDir);
    const realParentDir = await fs.realpath(path.dirname(candidatePath));
    this.assertPathInside(realParentDir, realPluginDir, 'Plugin template output parent resolves outside the plugin directory');

    try {
      const existingOutput = await fs.lstat(candidatePath);
      if (existingOutput.isSymbolicLink()) {
        throw new Error('Plugin template output file must not be a symbolic link');
      }

      if (!existingOutput.isFile()) {
        throw new Error('Plugin template output path must be a regular file when it already exists');
      }

      const realExistingOutput = await fs.realpath(candidatePath);
      this.assertPathInside(realExistingOutput, realPluginDir, 'Plugin template output file resolves outside the plugin directory');
    } catch (error: any) {
      if (error?.code !== 'ENOENT') {
        throw error;
      }
    }

    return candidatePath;
  }

  private async writePluginTemplateFile(pluginDir: string, fileName: string, content: string): Promise<void> {
    const outputPath = await this.resolvePluginTemplateOutputPath(pluginDir, fileName);
    const noFollowFlag = fsConstants.O_NOFOLLOW ?? 0;
    const handle = await fs.open(
      outputPath,
      fsConstants.O_WRONLY | fsConstants.O_CREAT | fsConstants.O_EXCL | noFollowFlag,
      0o666
    );

    try {
      await handle.writeFile(content);
    } finally {
      await handle.close();
    }
  }

  private async assertRealPathInsideProject(targetPath: string, message: string): Promise<void> {
    const realProjectRoot = await fs.realpath(this.projectRoot);
    const realTargetPath = await fs.realpath(targetPath);
    this.assertPathInside(realTargetPath, realProjectRoot, message);
  }

  private async realpathNearestExistingAncestor(targetPath: string): Promise<string> {
    let current = path.resolve(targetPath);

    while (true) {
      try {
        return await fs.realpath(current);
      } catch (error: any) {
        if (error?.code !== 'ENOENT') {
          throw error;
        }
      }

      const parent = path.dirname(current);
      if (parent === current) {
        throw new Error(`No existing ancestor found for ${targetPath}`);
      }
      current = parent;
    }
  }

  private assertPathInside(candidatePath: string, parentPath: string, message: string): void {
    const relative = path.relative(parentPath, candidatePath);
    if (relative === '') {
      return;
    }

    if (relative.startsWith('..') || path.isAbsolute(relative)) {
      throw new Error(message);
    }
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
            const module = await import(pathToFileURL(modulePath).href);
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
