/**
 * Hybrid Intent System
 *
 * Integrates CLI tools, MCP server, and Claude Code agents
 * for comprehensive Intent analysis and Phase 1 guidance
 */
export interface HybridIntentConfig {
    enableCLI: boolean;
    enableMCPServer: boolean;
    enableClaudeCodeIntegration: boolean;
    enforceRealTime: boolean;
    strictMode: boolean;
}
export declare class HybridIntentSystem {
    private agent?;
    private taskAdapter?;
    private metricsCollector;
    private config;
    private periodicCheckIntervalId?;
    constructor(config: HybridIntentConfig);
    /**
     * Main entry point for Intent operations
     * Routes requests to appropriate handler based on context
     */
    handleIntentRequest(request: {
        type: 'cli' | 'task' | 'mcp' | 'auto';
        data: any;
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
     * Proactive Intent monitoring and intervention
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
        requirementsTool: string;
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
    private executeIntentCommand;
    private executeMCPCommand;
    private combineResults;
    private generateCLIFollowUp;
    private generateAgentFollowUp;
    private setupRequirementWatchers;
    private setupGitIntegration;
    private startPeriodicChecks;
    /**
     * Clean up resources and stop periodic checks
     */
    cleanup(): void;
    private isRequirementFile;
    private handleRequirementChange;
    private checkIntentCompliance;
}
export declare const createHybridIntentSystem: (config?: Partial<HybridIntentConfig>) => HybridIntentSystem;
