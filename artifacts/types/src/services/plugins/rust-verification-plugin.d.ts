/**
 * Rust Verification MCP Plugin
 * Phase 2 of Issue #33: Enhanced Rust formal verification integration
 */
import type { MCPPlugin, MCPServer, MCPEndpoint } from '../mcp-server.js';
export interface RustVerificationPluginConfig {
    enabledTools: string[];
    defaultOptions: {
        timeout: number;
        memoryLimit: number;
        unwindLimit: number;
        strictMode: boolean;
        generateReport: boolean;
    };
    projectDiscovery: {
        autoDetect: boolean;
        searchDepth: number;
    };
}
export declare class RustVerificationPlugin implements MCPPlugin {
    name: string;
    version: string;
    description: string;
    private rustAgent;
    private verifyAgent;
    private config;
    constructor(config?: Partial<RustVerificationPluginConfig>);
    initialize(server: MCPServer): Promise<void>;
    terminate(server: MCPServer): Promise<void>;
    get endpoints(): MCPEndpoint[];
    private verifyRustProject;
    private getAvailableTools;
    private discoverRustProjects;
    private analyzeRustCode;
    private discoverSourceFiles;
    private generateVerificationSummary;
    private generateRecommendations;
    private getToolDescription;
    private findRustProjects;
    private performCodeAnalysis;
    private generateAnalysisRecommendations;
}
