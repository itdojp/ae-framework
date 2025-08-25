/**
 * Hybrid TDD System
 *
 * Integrates CLI tools, MCP server, and Claude Code agents
 * for comprehensive TDD enforcement and guidance
 */
export interface HybridTDDConfig {
    enableCLI: boolean;
    enableMCPServer: boolean;
    enableClaudeCodeIntegration: boolean;
    enforceRealTime: boolean;
    strictMode: boolean;
    enableSpecSSot: boolean;
    specPath: string;
    aeIrOutputPath: string;
}
export declare class HybridTDDSystem {
    private cli?;
    private taskAdapter?;
    private metricsCollector;
    private config;
    private specCompiler;
    private stateManager;
    constructor(config: HybridTDDConfig);
    /**
     * Main entry point for TDD operations
     * Routes requests to appropriate handler based on context
     */
    handleTDDRequest(request: {
        type: 'cli' | 'task' | 'mcp' | 'auto';
        data: any;
        phase?: number;
        context?: {
            isClaudeCode: boolean;
            hasTaskTool: boolean;
            userPreference: string;
        };
    }): Promise<{
        response: any;
        source: 'cli' | 'agent' | 'hybrid';
        followUp?: string[];
    }>;
    /**
     * AE-Spec/IR SSOT Pipeline Processing
     * Converts NL specs to structured IR for downstream phases
     */
    private processSpecPipeline;
    /**
     * Check if current phase requires spec pipeline processing
     */
    private requiresSpecPipeline;
    /**
     * Proactive TDD monitoring and intervention
     * Runs in background to provide real-time guidance
     */
    startProactiveMonitoring(): Promise<void>;
    /**
     * Integration with existing development workflow
     */
    integrateWithWorkflow(workflow: {
        ide: string;
        vcs: string;
        ci: string;
        testRunner: string;
    }): Promise<{
        integrations: Array<{
            type: string;
            status: 'active' | 'available' | 'unavailable';
            setup: string[];
        }>;
    }>;
    private detectBestHandler;
    private handleCLIRequest;
    private handleTaskRequest;
    private handleMCPRequest;
    private handleHybridRequest;
    private executeCLICommand;
    private executeMCPCommand;
    private combineResults;
    private generateCLIFollowUp;
    private generateAgentFollowUp;
    private setupFileWatchers;
    private setupGitIntegration;
    private startPeriodicChecks;
    private handleFileChange;
    private checkCompliance;
    private checkFileForViolations;
}
export declare const createHybridTDDSystem: (config?: Partial<HybridTDDConfig>) => HybridTDDSystem;
