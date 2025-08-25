/**
 * Container Agent - Phase 3 of Issue #37
 * Integrates container-based verification environments with the ae-framework
 */
import { ContainerManagerConfig } from '../services/container/container-manager.js';
export interface AgentResult<T = any> {
    success: boolean;
    message: string;
    data?: T;
    error?: string;
}
export interface ContainerAgentConfig extends ContainerManagerConfig {
    containerfilesPath?: string;
    registryConfig?: {
        url: string;
        username?: string;
        password?: string;
    };
    buildConfig?: {
        parallel: boolean;
        maxConcurrentBuilds: number;
        cacheEnabled: boolean;
    };
}
export interface ContainerVerificationRequest {
    projectPath: string;
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    jobName?: string;
    timeout?: number;
    buildImages?: boolean;
    environment?: Record<string, string>;
}
export interface ContainerBuildRequest {
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    baseImage?: string;
    tag?: string;
    push?: boolean;
    buildArgs?: Record<string, string>;
}
export interface ContainerStatusResult {
    engine: {
        name: string;
        version: string;
        available: boolean;
    };
    jobs: {
        active: number;
        completed: number;
        failed: number;
        total: number;
    };
    resources: {
        containers: number;
        images: number;
        volumes: number;
    };
    health: boolean;
}
export declare class ContainerAgent {
    private containerManager;
    private config;
    private initialized;
    constructor(config?: ContainerAgentConfig);
    /**
     * Initialize the container agent and underlying systems
     */
    initialize(): Promise<AgentResult>;
    /**
     * Run verification job in container
     */
    runVerification(request: ContainerVerificationRequest): Promise<AgentResult>;
    /**
     * Build verification container image
     */
    buildVerificationImage(request: ContainerBuildRequest): Promise<AgentResult>;
    /**
     * Get verification job status
     */
    getJobStatus(jobId: string): Promise<AgentResult>;
    /**
     * List verification jobs
     */
    listJobs(filter?: {
        status?: 'pending' | 'running' | 'completed' | 'failed';
        language?: string;
    }): Promise<AgentResult>;
    /**
     * Cancel running verification job
     */
    cancelJob(jobId: string): Promise<AgentResult>;
    /**
     * Get container agent and system status
     */
    getStatus(): Promise<AgentResult<ContainerStatusResult>>;
    /**
     * Cleanup old containers and resources
     */
    cleanup(options?: {
        maxAge?: number;
        keepCompleted?: number;
        force?: boolean;
    }): Promise<AgentResult>;
    /**
     * List available container engines
     */
    listEngines(): Promise<AgentResult>;
    /**
     * Shutdown container agent
     */
    shutdown(): Promise<AgentResult>;
    private ensureInitialized;
    private createDefaultContainerfiles;
    private setupEventHandlers;
}
