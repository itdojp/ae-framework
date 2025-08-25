/**
 * Container MCP Server - Phase 3 of Issue #37
 * MCP server providing container-based verification tools
 */
import { ContainerAgentConfig } from '../agents/container-agent.js';
export declare class ContainerServer {
    private server;
    private agent;
    constructor(config?: ContainerAgentConfig);
    private setupTools;
    private setupErrorHandling;
    start(): Promise<void>;
}
