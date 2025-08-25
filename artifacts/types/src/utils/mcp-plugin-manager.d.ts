/**
 * MCP Plugin Manager for ae-framework
 * Manages loading, registration, and lifecycle of MCP plugins
 */
import { MCPPlugin, MCPServer } from '../services/mcp-server.js';
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
export declare class MCPPluginManager {
    private plugins;
    private pluginPaths;
    private projectRoot;
    private server?;
    constructor(projectRoot: string, pluginPaths?: string[]);
    /**
     * Set the MCP server instance for plugin registration
     */
    setServer(server: MCPServer): void;
    /**
     * Discover all available plugins
     */
    discoverPlugins(options?: Partial<PluginDiscoveryOptions>): Promise<PluginManifest[]>;
    /**
     * Load a plugin from its manifest
     */
    loadPlugin(manifest: PluginManifest, filePath: string): Promise<PluginLoadResult>;
    /**
     * Load plugins from directory
     */
    loadPluginsFromDirectory(directoryPath: string): Promise<PluginLoadResult[]>;
    /**
     * Enable a plugin
     */
    enablePlugin(name: string): Promise<boolean>;
    /**
     * Disable a plugin
     */
    disablePlugin(name: string): Promise<boolean>;
    /**
     * Unload a plugin
     */
    unloadPlugin(name: string): Promise<boolean>;
    /**
     * Get all loaded plugins
     */
    getLoadedPlugins(): PluginRegistration[];
    /**
     * Get plugin by name
     */
    getPlugin(name: string): PluginRegistration | undefined;
    /**
     * Get enabled plugins
     */
    getEnabledPlugins(): PluginRegistration[];
    /**
     * Create a new plugin template
     */
    createPluginTemplate(name: string, targetDir: string): Promise<void>;
    private scanPluginDirectory;
    private validateManifest;
    private loadPluginModule;
}
