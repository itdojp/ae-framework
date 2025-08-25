/**
 * Container Manager - Container Lifecycle Management
 * Phase 3 of Issue #37: Orchestrates container operations across different engines
 */
import { EventEmitter } from 'events';
import { ContainerLogs, type ContainerEngineName } from './container-engine.js';
export interface ContainerManagerConfig {
    preferredEngine?: ContainerEngineName;
    autoCleanup?: boolean;
    maxConcurrentContainers?: number;
    defaultTimeout?: number;
    resourceLimits?: {
        memory?: string;
        cpus?: string;
    };
    securityDefaults?: {
        rootless?: boolean;
        readOnlyRootFilesystem?: boolean;
        noNewPrivileges?: boolean;
    };
}
export interface VerificationEnvironment {
    name: string;
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    baseImage: string;
    resources: {
        memory: string;
        cpus: string;
    };
    volumes: Array<{
        source: string;
        target: string;
        readonly?: boolean;
    }>;
    environment: Record<string, string>;
}
export interface VerificationJob {
    id: string;
    name: string;
    projectPath: string;
    language: 'rust' | 'elixir' | 'multi';
    tools: string[];
    containerId?: string;
    status: 'pending' | 'running' | 'completed' | 'failed';
    startTime?: Date;
    endTime?: Date;
    results?: any;
    logs?: ContainerLogs;
    error?: string;
}
export interface ContainerHealthCheck {
    containerId: string;
    healthy: boolean;
    lastCheck: Date;
    checks: {
        running: boolean;
        responsive: boolean;
        resourceUsage: {
            cpu: number;
            memory: number;
        };
    };
}
export declare class ContainerManager extends EventEmitter {
    private engine;
    private config;
    private activeJobs;
    private healthChecks;
    private cleanupTimer?;
    private healthCheckTimer?;
    constructor(config?: ContainerManagerConfig);
    /**
     * Initialize the container manager
     */
    initialize(): Promise<void>;
    /**
     * Create a verification environment
     */
    createVerificationEnvironment(env: VerificationEnvironment): Promise<string>;
    /**
     * Run verification job in container
     */
    runVerificationJob(job: Omit<VerificationJob, 'id' | 'status' | 'startTime'>): Promise<VerificationJob>;
    /**
     * Get job status
     */
    getJob(jobId: string): VerificationJob | undefined;
    /**
     * List all jobs
     */
    listJobs(filter?: {
        status?: VerificationJob['status'];
        language?: string;
    }): VerificationJob[];
    /**
     * Cancel a running job
     */
    cancelJob(jobId: string): Promise<void>;
    /**
     * Build verification container image
     */
    buildVerificationImage(language: 'rust' | 'elixir' | 'multi', tools: string[], options?: {
        tag?: string;
        buildArgs?: Record<string, string>;
        push?: boolean;
    }): Promise<string>;
    /**
     * Get container engine information
     */
    getEngineInfo(): import("./container-engine.js").ContainerEngineInfo;
    /**
     * List available container engines
     */
    listAvailableEngines(): Promise<import("./container-engine.js").ContainerEngineInfo[]>;
    /**
     * Get system health status
     */
    getHealthStatus(): Promise<{
        healthy: boolean;
        engine: {
            name: string;
            version: string;
            available: boolean;
        };
        jobs: {
            total: number;
            running: number;
            completed: number;
            failed: number;
        };
        resources: {
            activeContainers: number;
            images: number;
            volumes: number;
        };
    }>;
    /**
     * Cleanup old jobs and containers
     */
    cleanup(options?: {
        maxAge?: number;
        keepCompleted?: number;
        force?: boolean;
    }): Promise<{
        jobsRemoved: number;
        containersRemoved: number;
        spaceSaved: number;
    }>;
    /**
     * Shutdown the container manager
     */
    shutdown(): Promise<void>;
    private setupEngineEventListeners;
    private startBackgroundServices;
    private stopBackgroundServices;
    private getVerificationEnvironment;
    private buildVerificationCommand;
    private buildRustVerificationScript;
    private buildElixirVerificationScript;
    private buildMultiLanguageVerificationScript;
    private parseVerificationResults;
}
