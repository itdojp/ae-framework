/**
 * Container Engine Abstraction Layer
 * Phase 3 of Issue #37: Unified interface for Docker and Podman container engines
 */

import type { EventEmitter } from 'events';

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
  memory?: string;      // e.g., "512m", "1g"
  cpus?: string;        // e.g., "0.5", "2"
  cpuShares?: number;   // CPU shares (relative weight)
  diskSpace?: string;   // e.g., "1g", "500m"
  maxProcesses?: number;
}

export interface VolumeMount {
  source: string;       // Host path or named volume
  target: string;       // Container path
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
  user?: string;        // UID:GID or username
  group?: string;       // Group name or GID
  capabilities?: {
    add?: string[];     // Add capabilities
    drop?: string[];    // Drop capabilities
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
  timeout?: number;     // Timeout in seconds
  capture?: boolean;    // Capture output
  stream?: boolean;     // Stream output in real-time
  cleanup?: boolean;    // Auto-cleanup on completion
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
    usage: number;      // Percentage
    systemUsage: number;
  };
  memory: {
    usage: number;      // Bytes
    limit: number;
    percentage: number;
  };
  network: {
    rx: number;         // Bytes received
    tx: number;         // Bytes transmitted
  };
  io: {
    read: number;       // Bytes read
    write: number;      // Bytes written
  };
  timestamp: Date;
}

export interface ImageBuildContext {
  contextPath: string;
  dockerfilePath?: string;    // Relative to context
  target?: string;           // Multi-stage build target
  buildArgs?: Record<string, string>;
  labels?: Record<string, string>;
  platforms?: string[];      // Multi-platform builds
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
export abstract class ContainerEngine extends EventEmitter {
  protected engineInfo: ContainerEngineInfo;

  constructor(engineInfo: ContainerEngineInfo) {
    super();
    this.engineInfo = engineInfo;
  }

  // Engine information
  getEngineInfo(): ContainerEngineInfo {
    return { ...this.engineInfo };
  }

  getName(): ContainerEngineName {
    return this.engineInfo.name;
  }

  getVersion(): string {
    return this.engineInfo.version;
  }

  isAvailable(): boolean {
    return this.engineInfo.available;
  }

  getCapabilities(): ContainerCapabilities {
    return { ...this.engineInfo.capabilities };
  }

  // Abstract methods to be implemented by concrete engines
  abstract checkAvailability(): Promise<boolean>;
  
  // Container lifecycle
  abstract createContainer(config: ContainerConfig): Promise<string>;
  abstract startContainer(containerId: string, options?: ContainerRunOptions): Promise<void>;
  abstract stopContainer(containerId: string, timeout?: number): Promise<void>;
  abstract removeContainer(containerId: string, force?: boolean): Promise<void>;
  abstract restartContainer(containerId: string): Promise<void>;
  
  // Container operations
  abstract runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<{
    containerId: string;
    exitCode: number;
    output: ContainerLogs;
  }>;
  
  abstract executeInContainer(
    containerId: string, 
    command: string[], 
    options?: { user?: string; workingDir?: string; environment?: Record<string, string> }
  ): Promise<{
    exitCode: number;
    output: ContainerLogs;
  }>;
  
  // Container inspection
  abstract getContainerStatus(containerId: string): Promise<ContainerStatus>;
  abstract listContainers(filters?: Record<string, string>): Promise<ContainerStatus[]>;
  abstract getContainerLogs(containerId: string, options?: { 
    tail?: number; 
    since?: Date; 
    follow?: boolean;
  }): Promise<ContainerLogs | AsyncIterable<string>>;
  abstract getContainerStats(containerId: string): Promise<ContainerStats>;
  
  // Image management
  abstract buildImage(
    buildContext: ImageBuildContext, 
    imageTag: string
  ): Promise<string>;
  abstract pullImage(image: string, tag?: string): Promise<void>;
  abstract pushImage(image: string, tag?: string): Promise<void>;
  abstract removeImage(image: string, force?: boolean): Promise<void>;
  abstract listImages(filters?: Record<string, string>): Promise<ImageInfo[]>;
  abstract tagImage(sourceImage: string, targetImage: string): Promise<void>;
  
  // Volume management
  abstract createVolume(name: string, labels?: Record<string, string>): Promise<void>;
  abstract removeVolume(name: string, force?: boolean): Promise<void>;
  abstract listVolumes(): Promise<Array<{
    name: string;
    driver: string;
    mountpoint: string;
    labels?: Record<string, string>;
    size?: number;
  }>>;
  
  // Network management  
  abstract createNetwork(
    name: string, 
    options?: { driver?: string; subnet?: string; gateway?: string; labels?: Record<string, string> }
  ): Promise<void>;
  abstract removeNetwork(name: string): Promise<void>;
  abstract listNetworks(): Promise<Array<{
    id: string;
    name: string;
    driver: string;
    subnet?: string;
    gateway?: string;
    labels?: Record<string, string>;
  }>>;
  
  // Compose/Pod operations (if supported)
  abstract supportsCompose(): boolean;
  abstract runCompose?(composeFile: string, options?: { 
    projectName?: string; 
    environment?: Record<string, string>;
    detached?: boolean;
  }): Promise<void>;
  abstract stopCompose?(composeFile: string, projectName?: string): Promise<void>;
  
  // Cleanup and maintenance
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
  
  // Utility methods
  protected validateContainerName(name: string): boolean {
    return /^[a-zA-Z0-9][a-zA-Z0-9_.-]*$/.test(name);
  }
  
  protected buildCommandArgs(config: ContainerConfig): string[] {
    const args: string[] = [];
    
    // Basic container options
    if (config.name) args.push('--name', config.name);
    if (config.detached !== false) args.push('--detach');
    if (config.interactive) args.push('--interactive');
    if (config.tty) args.push('--tty');
    if (config.autoRemove) args.push('--rm');
    
    // Environment variables
    if (config.environment) {
      Object.entries(config.environment).forEach(([key, value]) => {
        args.push('--env', `${key}=${value}`);
      });
    }
    
    // Working directory
    if (config.workingDir) args.push('--workdir', config.workingDir);
    
    // Volume mounts
    if (config.volumes) {
      config.volumes.forEach(volume => {
        let mountStr = `${volume.source}:${volume.target}`;
        if (volume.readonly) mountStr += ':ro';
        args.push('--volume', mountStr);
      });
    }
    
    // Port mappings
    if (config.ports) {
      config.ports.forEach(port => {
        let portStr = '';
        if (port.hostIp) portStr += `${port.hostIp}:`;
        if (port.hostPort) portStr += `${port.hostPort}:`;
        portStr += `${port.containerPort}`;
        if (port.protocol && port.protocol !== 'tcp') portStr += `/${port.protocol}`;
        args.push('--publish', portStr);
      });
    }
    
    // Resource limits
    if (config.resources) {
      const res = config.resources;
      if (res.memory) args.push('--memory', res.memory);
      if (res.cpus) args.push('--cpus', res.cpus);
      if (res.cpuShares) args.push('--cpu-shares', res.cpuShares.toString());
    }
    
    // Security context
    if (config.security) {
      const sec = config.security;
      if (sec.user) args.push('--user', sec.user);
      if (sec.noNewPrivileges) args.push('--security-opt', 'no-new-privileges');
      if (sec.readOnlyRootFilesystem) args.push('--read-only');
      if (sec.capabilities?.add) {
        sec.capabilities.add.forEach(cap => {
          args.push('--cap-add', cap);
        });
      }
      if (sec.capabilities?.drop) {
        sec.capabilities.drop.forEach(cap => {
          args.push('--cap-drop', cap);
        });
      }
    }
    
    // Network configuration
    if (config.network) {
      args.push('--network', config.network.mode);
    }
    
    // Labels
    if (config.labels) {
      Object.entries(config.labels).forEach(([key, value]) => {
        args.push('--label', `${key}=${value}`);
      });
    }
    
    // Health check
    if (config.healthCheck) {
      const health = config.healthCheck;
      args.push('--health-cmd', health.command.join(' '));
      if (health.interval) args.push('--health-interval', health.interval);
      if (health.timeout) args.push('--health-timeout', health.timeout);
      if (health.retries) args.push('--health-retries', health.retries.toString());
      if (health.startPeriod) args.push('--health-start-period', health.startPeriod);
    }
    
    // Restart policy
    if (config.restart) args.push('--restart', config.restart);
    
    return args;
  }
  
  protected parseContainerStatus(statusOutput: string): Partial<ContainerStatus> {
    // To be implemented by concrete engines based on their output format
    return {};
  }
  
  protected formatResourceLimits(resources: ResourceLimits): Record<string, string> {
    const formatted: Record<string, string> = {};
    
    if (resources.memory) formatted.memory = resources.memory;
    if (resources.cpus) formatted.cpus = resources.cpus;
    if (resources.cpuShares) formatted.cpuShares = resources.cpuShares.toString();
    
    return formatted;
  }
}

/**
 * Container engine factory
 */
export class ContainerEngineFactory {
  private static detectedEngines: ContainerEngineInfo[] = [];
  
  static async detectAvailableEngines(): Promise<ContainerEngineInfo[]> {
    if (this.detectedEngines.length > 0) {
      return this.detectedEngines;
    }
    
    const engines: ContainerEngineInfo[] = [];
    
    // Check for Podman
    try {
      const { PodmanEngine } = await import('./podman-engine.js');
      const podmanEngine = new PodmanEngine();
      if (await podmanEngine.checkAvailability()) {
        engines.push(podmanEngine.getEngineInfo());
      }
    } catch (error) {
      console.warn('Podman detection failed:', error);
    }
    
    // Check for Docker
    try {
      const { DockerEngine } = await import('./docker-engine.js');
      const dockerEngine = new DockerEngine();
      if (await dockerEngine.checkAvailability()) {
        engines.push(dockerEngine.getEngineInfo());
      }
    } catch (error) {
      console.warn('Docker detection failed:', error);
    }
    
    this.detectedEngines = engines;
    return engines;
  }
  
  static async createEngine(engineName: ContainerEngineName): Promise<ContainerEngine> {
    switch (engineName) {
      case 'podman':
        const { PodmanEngine } = await import('./podman-engine.js');
        return new PodmanEngine();
        
      case 'docker':
        const { DockerEngine } = await import('./docker-engine.js');
        return new DockerEngine();
        
      default:
        throw new Error(`Unsupported container engine: ${engineName}`);
    }
  }
  
  static async createPreferredEngine(): Promise<ContainerEngine> {
    const engines = await this.detectAvailableEngines();
    
    if (engines.length === 0) {
      throw new Error('No container engines available. Please install Docker or Podman.');
    }
    
    // Prefer Podman for security (rootless by default)
    const podman = engines.find(e => e.name === 'podman');
    if (podman) {
      return this.createEngine('podman');
    }
    
    // Fallback to Docker
    const docker = engines.find(e => e.name === 'docker');
    if (docker) {
      return this.createEngine('docker');
    }
    
    throw new Error('No supported container engines found');
  }
  
  static clearCache(): void {
    this.detectedEngines = [];
  }
}