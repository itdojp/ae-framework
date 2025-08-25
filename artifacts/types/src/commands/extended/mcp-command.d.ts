/**
 * MCP Command for ae-framework
 * Manages MCP server instances, plugins, and extensions
 */
import { BaseExtendedCommand, ExtendedCommandResult, ExtendedCommandConfig } from './base-command.js';
export interface MCPCommandResult extends ExtendedCommandResult {
    serverStatus?: any;
    pluginList?: string[];
    capabilities?: any[];
    metrics?: any;
    pluginDetails?: any;
    recommendations?: string[];
}
export declare class MCPCommand extends BaseExtendedCommand {
    readonly name = "/ae:mcp";
    readonly description = "Manage MCP server, plugins, and extensions";
    readonly category: "utility";
    readonly usage = "/ae:mcp <action> [options]";
    readonly aliases: string[];
    private mcpServer?;
    private pluginManager?;
    private contextManager?;
    private tokenOptimizer?;
    constructor(config?: ExtendedCommandConfig);
    private getMCPServer;
    private getPluginManager;
    private getContextManager;
    private getTokenOptimizer;
    handler(args: string[], context: any): Promise<MCPCommandResult>;
    private handleStartServer;
    private handleStopServer;
    private handleRestartServer;
    private handleServerStatus;
    private handlePluginManagement;
    private handleListPlugins;
    private handleCapabilities;
    private handleMetrics;
    private handleConfigManagement;
    private handleShowConfig;
    private handleHelp;
    private loadServerConfig;
    private handleDiscoverPlugins;
    private handleLoadPlugin;
    private handleEnablePlugin;
    private handleDisablePlugin;
    private handleUnloadPlugin;
    private handleCreatePlugin;
    private handleCreateConfig;
    private createErrorResult;
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected execute(args: string[], options: Record<string, any>, context: any): Promise<ExtendedCommandResult>;
    protected generateValidationClaim(data: any): string;
    protected generateSummary(data: any): string;
}
