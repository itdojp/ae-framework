/**
 * Podman Container Engine Implementation
 * Phase 3 of Issue #37: Podman-specific container engine implementation
 */
import { ContainerEngine, ContainerConfig, ContainerRunOptions, ContainerStatus, ContainerLogs, ContainerStats, ImageBuildContext, ImageInfo } from './container-engine.js';
export declare class PodmanEngine extends ContainerEngine {
    private podmanPath;
    private composePath?;
    constructor();
    checkAvailability(): Promise<boolean>;
    createContainer(config: ContainerConfig): Promise<string>;
    startContainer(containerId: string, options?: ContainerRunOptions): Promise<void>;
    stopContainer(containerId: string, timeout?: number): Promise<void>;
    removeContainer(containerId: string, force?: boolean): Promise<void>;
    restartContainer(containerId: string): Promise<void>;
    runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<{
        containerId: string;
        exitCode: number;
        output: ContainerLogs;
    }>;
    executeInContainer(containerId: string, command: string[], options?: {
        user?: string;
        workingDir?: string;
        environment?: Record<string, string>;
    }): Promise<{
        exitCode: number;
        output: ContainerLogs;
    }>;
    getContainerStatus(containerId: string): Promise<ContainerStatus>;
    listContainers(filters?: Record<string, string>): Promise<ContainerStatus[]>;
    getContainerLogs(containerId: string, options?: {
        tail?: number;
        since?: Date;
        follow?: boolean;
    }): Promise<ContainerLogs | AsyncIterable<string>>;
    private streamLogs;
    getContainerStats(containerId: string): Promise<ContainerStats>;
    buildImage(buildContext: ImageBuildContext, imageTag: string): Promise<string>;
    pullImage(image: string, tag?: string): Promise<void>;
    pushImage(image: string, tag?: string): Promise<void>;
    removeImage(image: string, force?: boolean): Promise<void>;
    listImages(filters?: Record<string, string>): Promise<ImageInfo[]>;
    tagImage(sourceImage: string, targetImage: string): Promise<void>;
    createVolume(name: string, labels?: Record<string, string>): Promise<void>;
    removeVolume(name: string, force?: boolean): Promise<void>;
    listVolumes(): Promise<Array<{
        name: string;
        driver: string;
        mountpoint: string;
        labels?: Record<string, string>;
        size?: number;
    }>>;
    createNetwork(name: string, options?: {
        driver?: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }): Promise<void>;
    removeNetwork(name: string): Promise<void>;
    listNetworks(): Promise<Array<{
        id: string;
        name: string;
        driver: string;
        subnet?: string;
        gateway?: string;
        labels?: Record<string, string>;
    }>>;
    supportsCompose(): boolean;
    runCompose(composeFile: string, options?: {
        projectName?: string;
        environment?: Record<string, string>;
        detached?: boolean;
    }): Promise<void>;
    stopCompose(composeFile: string, projectName?: string): Promise<void>;
    cleanup(options?: {
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
    private mapPodmanState;
    private parsePorts;
    private parseSize;
}
