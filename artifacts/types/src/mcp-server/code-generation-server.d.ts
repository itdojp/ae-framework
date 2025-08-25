/**
 * MCP Server for Code Generation Agent
 * Provides tools for Phase 4: Code generation from tests
 */
export declare class CodeGenerationServer {
    private server;
    private agent;
    constructor();
    private setupErrorHandling;
    private registerTools;
    private validateCodeAgainstTests;
    start(): Promise<void>;
    stop(): Promise<void>;
}
