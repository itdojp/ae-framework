/**
 * Container Engine Abstraction Layer
 * Phase 3 of Issue #37: Unified interface for Docker and Podman container engines
 */
import { EventEmitter } from 'events';
export type ContainerEngineName = 'docker' | 'podman';
export interface ContainerCapabilities {
    rootless: boolean;
    compose: boolean;
    buildx: boolean;
    systemd: boolean;
    selinux: boolean;
    pods: boolean;
}
export interface ContainerEngineInfo {
    name: ContainerEngineName;
    version: string;
    available: boolean;
    capabilities: ContainerCapabilities;
    executable: string;
    composeCommand?: string;
}
export interface ResourceLimits {
    memory?: string;
    cpus?: string;
    cpuShares?: number;
    diskSpace?: string;
    maxProcesses?: number;
}
export interface VolumeMount {
    source: string;
    target: string;
    readonly?: boolean;
    type?: 'bind' | 'volume' | 'tmpfs';
}
export interface PortMapping {
    containerPort: number;
    hostPort?: number;
    protocol?: 'tcp' | 'udp';
    hostIp?: string;
}
export interface ContainerNetworkConfig {
    mode: 'bridge' | 'host' | 'none' | 'container' | 'custom';
    customNetworkName?: string;
    isolation?: boolean;
}
export interface SecurityContext {
    user?: string;
    group?: string;
    capabilities?: {
        add?: string[];
        drop?: string[];
    };
    seLinuxLabel?: string;
    appArmor?: string;
    seccomp?: string;
    noNewPrivileges?: boolean;
    readOnlyRootFilesystem?: boolean;
}
export interface ContainerConfig {
    name: string;
    image: string;
    tag?: string;
    command?: string[];
    args?: string[];
    environment?: Record<string, string>;
    workingDir?: string;
    volumes?: VolumeMount[];
    ports?: PortMapping[];
    resources?: ResourceLimits;
    network?: ContainerNetworkConfig;
    security?: SecurityContext;
    labels?: Record<string, string>;
    healthCheck?: {
        command: string[];
        interval?: string;
        timeout?: string;
        retries?: number;
        startPeriod?: string;
    };
    restart?: 'no' | 'always' | 'unless-stopped' | 'on-failure';
    autoRemove?: boolean;
    interactive?: boolean;
    tty?: boolean;
    detached?: boolean;
}
export interface ContainerRunOptions {
    timeout?: number;
    capture?: boolean;
    stream?: boolean;
    cleanup?: boolean;
}
export interface ContainerStatus {
    id: string;
    name: string;
    state: 'created' | 'running' | 'paused' | 'restarting' | 'removing' | 'exited' | 'dead';
    status: string;
    image: string;
    ports?: PortMapping[];
    createdAt: Date;
    startedAt?: Date;
    finishedAt?: Date;
    exitCode?: number;
    error?: string;
    health?: 'healthy' | 'unhealthy' | 'starting' | 'none';
}
export interface ContainerLogs {
    stdout: string;
    stderr: string;
    combined: string;
    timestamp: Date;
}
export interface ContainerStats {
    cpu: {
        usage: number;
        systemUsage: number;
    };
    memory: {
        usage: number;
        limit: number;
        percentage: number;
    };
    network: {
        rx: number;
        tx: number;
    };
    io: {
        read: number;
        write: number;
    };
    timestamp: Date;
}
export interface ImageBuildContext {
    contextPath: string;
    dockerfilePath?: string;
    target?: string;
    buildArgs?: Record<string, string>;
    labels?: Record<string, string>;
    platforms?: string[];
    cache?: boolean;
    squash?: boolean;
    pullBaseImage?: boolean;
}
export interface ImageInfo {
    id: string;
    repository: string;
    tag: string;
    digest?: string;
    size: number;
    created: Date;
    labels?: Record<string, string>;
}
/**
 * Abstract base class for container engines
 */
export declare abstract class ContainerEngine extends EventEmitter {
    protected engineInfo: ContainerEngineInfo;
    constructor(engineInfo: ContainerEngineInfo);
    getEngineInfo(): ContainerEngineInfo;
    getName(): ContainerEngineName;
    getVersion(): string;
    isAvailable(): boolean;
    getCapabilities(): ContainerCapabilities;
    abstract checkAvailability(): Promise<boolean>;
    abstract createContainer(config: ContainerConfig): Promise<string>;
    abstract startContainer(containerId: string, options?: ContainerRunOptions): Promise<void>;
    abstract stopContainer(containerId: string, timeout?: number): Promise<void>;
    abstract removeContainer(containerId: string, force?: boolean): Promise<void>;
    abstract restartContainer(containerId: string): Promise<void>;
    abstract runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<{
        containerId: string;
        exitCode: number;
        output: ContainerLogs;
    }>;
    abstract executeInContainer(containerId: string, command: string[], options?: {
        user?: string;
        workingDir?: string;
        environment?: Record<string, string>;
    }): Promise<{
        exitCode: number;
        output: ContainerLogs;
    }>;
    abstract getContainerStatus(containerId: string): Promise<ContainerStatus>;
    abstract listContainers(filters?: Record<string, string>): Promise<ContainerStatus[]>;
    abstract getContainerLogs(containerId: string, options?: {
        tail?: number;
        since?: Date;
        follow?: boolean;
    }): Promise<ContainerLogs | AsyncIterable<string>>;
    abstract getContainerStats(containerId: string): Promise<ContainerStats>;
    abstract buildImage(buildContext: ImageBuildContext, imageTag: string): Promise<string>;
    abstract pullImage(image: string, tag?: string): Promise<void>;
    abstract pushImage(image: string, tag?: string): Promise<void>;
    abstract removeImage(image: string, force?: boolean): Promise<void>;
    abstract listImages(filters?: Record<string, string>): Promise<ImageInfo[]>;
    abstract tagImage(sourceImage: string, targetImage: string): Promise<void>;
    abstract createVolume(name: string, labels?: Record<string, string>): Promise<void>;
    abstract removeVolume(name: string, force?: boolean): Promise<void>;
    abstract listVolumes(): Promise<Array<{
        name: string;
        driver: string;
        mountpoint: string;
        labels?: Record<string, string>;
        size?: number;
    }>>;
    abstract createNetwork(name: string, options?: {
        driver?: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }): Promise<void>;
    abstract removeNetwork(name: string): Promise<void>;
    abstract listNetworks(): Promise<Array<{
        id: string;
        name: string;
        driver: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }>>;
    abstract supportsCompose(): boolean;
    abstract runCompose?(composeFile: string, options?: {
        projectName?: string;
        environment?: Record<string, string>;
        detached?: boolean;
    }): Promise<void>;
    abstract stopCompose?(composeFile: string, projectName?: string): Promise<void>;
    abstract cleanup(options?: {
        containers?: boolean;
        images?: boolean;
        volumes?: boolean;
        networks?: boolean;
        force?: boolean;
    }): Promise<{
        containers: number;
        images: number;
        volumes: number;
        networks: number;
        spaceSaved: number;
    }>;
    protected validateContainerName(name: string): boolean;
    protected buildCommandArgs(config: ContainerConfig): string[];
    protected parseContainerStatus(statusOutput: string): Partial<ContainerStatus>;
    protected formatResourceLimits(resources: ResourceLimits): Record<string, string>;
}
/**
 * Container engine factory
 */
export declare class ContainerEngineFactory {
    private static detectedEngines;
    static detectAvailableEngines(): Promise<ContainerEngineInfo[]>;
    static createEngine(engineName: ContainerEngineName): Promise<ContainerEngine>;
    static createPreferredEngine(): Promise<ContainerEngine>;
    static clearCache(): void;
}
