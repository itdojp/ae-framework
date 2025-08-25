#!/usr/bin/env node
/**
 * MCP Server for Formal Agent
 * Provides tools for formal specification generation, validation, and model checking
 */
declare class FormalMCPServer {
    private server;
    private formalAgent;
    constructor();
    private setupToolHandlers;
    private handleGenerateFormalSpec;
    private handleCreateAPISpec;
    private handleGenerateStateMachine;
    private handleCreateContracts;
    private handleValidateSpec;
    private handleModelCheck;
    private handleGenerateDiagrams;
    private handleListSpecifications;
    private handleGetSpecification;
    private handleUpdateConfig;
    private setupErrorHandling;
    run(): Promise<void>;
}
export declare function createFormalServer(): Promise<FormalMCPServer>;
export { FormalMCPServer };
