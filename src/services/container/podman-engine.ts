/**
 * Podman Container Engine Implementation
 * Phase 3 of Issue #37: Podman-specific container engine implementation
 */

import { execSync, exec, spawn } from 'child_process';
import { promisify } from 'util';
import * as path from 'path';
import * as fs from 'fs/promises';
import { 
  ContainerEngine, 
  ContainerEngineInfo, 
  ContainerConfig, 
  ContainerRunOptions, 
  ContainerStatus, 
  ContainerLogs, 
  ContainerStats,
  ImageBuildContext,
  ImageInfo,
  type ContainerCapabilities
} from './container-engine.js';

const execAsync = promisify(exec);

export class PodmanEngine extends ContainerEngine {
  private podmanPath: string = 'podman';
  private composePath?: string;

  constructor() {
    const engineInfo: ContainerEngineInfo = {
      name: 'podman',
      version: '',
      available: false,
      executable: 'podman',
      capabilities: {
        rootless: true,
        compose: false,
        buildx: false,
        systemd: true,
        selinux: true,
        pods: true
      }
    };

    super(engineInfo);
  }

  async checkAvailability(): Promise<boolean> {
    try {
      // Check if podman is available
      const versionResult = await execAsync(`${this.podmanPath} --version`);
      const versionMatch = versionResult.stdout.match(/podman version (\d+\.\d+\.\d+)/);
      
      if (!versionMatch) {
        this.engineInfo.available = false;
        return false;
      }

      this.engineInfo.version = versionMatch[1];
      this.engineInfo.available = true;

      // Check for podman-compose
      try {
        await execAsync('podman-compose --version');
        this.engineInfo.composeCommand = 'podman-compose';
        this.engineInfo.capabilities.compose = true;
        this.composePath = 'podman-compose';
      } catch {
        // Check for docker-compose with podman
        try {
          await execAsync('docker-compose --version');
          this.engineInfo.composeCommand = 'docker-compose';
          this.engineInfo.capabilities.compose = true;
          this.composePath = 'docker-compose';
        } catch {
          console.warn('No compose tool found for Podman');
        }
      }

      // Check if running rootless
      try {
        const infoResult = await execAsync(`${this.podmanPath} info --format json`);
        const info = JSON.parse(infoResult.stdout);
        this.engineInfo.capabilities.rootless = !info.host?.security?.rootless === false;
      } catch {
        // Assume rootless if we can't determine
        this.engineInfo.capabilities.rootless = true;
      }

      return true;
    } catch (error) {
      this.engineInfo.available = false;
      return false;
    }
  }

  async createContainer(config: ContainerConfig): Promise<string> {
    if (!this.isAvailable()) {
      throw new Error('Podman is not available');
    }

    if (!this.validateContainerName(config.name)) {
      throw new Error(`Invalid container name: ${config.name}`);
    }

    const args = ['create'];
    args.push(...this.buildCommandArgs(config));

    // Add the image
    const imageTag = config.tag ? `${config.image}:${config.tag}` : config.image;
    args.push(imageTag);

    // Add command and args
    if (config.command) args.push(...config.command);
    if (config.args) args.push(...config.args);

    try {
      const result = await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      const containerId = result.stdout.trim();
      
      this.emit('containerCreated', {
        containerId,
        name: config.name,
        image: imageTag
      });

      return containerId;
    } catch (error: any) {
      this.emit('error', {
        operation: 'createContainer',
        error: error.message,
        config
      });
      throw new Error(`Failed to create container: ${error.message}`);
    }
  }

  async startContainer(containerId: string, options?: ContainerRunOptions): Promise<void> {
    try {
      const args = ['start'];
      if (options?.capture) args.push('--attach');
      args.push(containerId);

      await execAsync(`${this.podmanPath} ${args.join(' ')}`, {
        timeout: (options?.timeout || 60) * 1000
      });

      this.emit('containerStarted', { containerId });
    } catch (error: any) {
      this.emit('error', {
        operation: 'startContainer',
        error: error.message,
        containerId
      });
      throw new Error(`Failed to start container: ${error.message}`);
    }
  }

  async stopContainer(containerId: string, timeout: number = 10): Promise<void> {
    try {
      await execAsync(`${this.podmanPath} stop --time ${timeout} ${containerId}`);
      
      this.emit('containerStopped', { containerId });
    } catch (error: any) {
      this.emit('error', {
        operation: 'stopContainer',
        error: error.message,
        containerId
      });
      throw new Error(`Failed to stop container: ${error.message}`);
    }
  }

  async removeContainer(containerId: string, force: boolean = false): Promise<void> {
    try {
      const args = ['rm'];
      if (force) args.push('--force');
      args.push(containerId);

      await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      
      this.emit('containerRemoved', { containerId, force });
    } catch (error: any) {
      this.emit('error', {
        operation: 'removeContainer',
        error: error.message,
        containerId
      });
      throw new Error(`Failed to remove container: ${error.message}`);
    }
  }

  async restartContainer(containerId: string): Promise<void> {
    try {
      await execAsync(`${this.podmanPath} restart ${containerId}`);
      
      this.emit('containerRestarted', { containerId });
    } catch (error: any) {
      this.emit('error', {
        operation: 'restartContainer',
        error: error.message,
        containerId
      });
      throw new Error(`Failed to restart container: ${error.message}`);
    }
  }

  async runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<{
    containerId: string;
    exitCode: number;
    output: ContainerLogs;
  }> {
    const args = ['run'];
    
    // Force removal after run if cleanup is requested
    if (options?.cleanup !== false) args.push('--rm');
    
    args.push(...this.buildCommandArgs(config));

    // Add the image
    const imageTag = config.tag ? `${config.image}:${config.tag}` : config.image;
    args.push(imageTag);

    // Add command and args
    if (config.command) args.push(...config.command);
    if (config.args) args.push(...config.args);

    try {
      const result = await execAsync(`${this.podmanPath} ${args.join(' ')}`, {
        timeout: (options?.timeout || 300) * 1000,
        maxBuffer: 10 * 1024 * 1024 // 10MB buffer
      });

      const logs: ContainerLogs = {
        stdout: result.stdout,
        stderr: result.stderr,
        combined: result.stdout + result.stderr,
        timestamp: new Date()
      };

      this.emit('containerRun', {
        config,
        exitCode: 0,
        output: logs
      });

      return {
        containerId: 'ephemeral-' + Date.now(), // Podman run --rm doesn't return container ID
        exitCode: 0,
        output: logs
      };
    } catch (error: any) {
      const logs: ContainerLogs = {
        stdout: error.stdout || '',
        stderr: error.stderr || error.message,
        combined: (error.stdout || '') + (error.stderr || error.message),
        timestamp: new Date()
      };

      this.emit('error', {
        operation: 'runContainer',
        error: error.message,
        config,
        output: logs
      });

      return {
        containerId: 'failed-' + Date.now(),
        exitCode: error.code || 1,
        output: logs
      };
    }
  }

  async executeInContainer(
    containerId: string,
    command: string[],
    options?: { user?: string; workingDir?: string; environment?: Record<string, string> }
  ): Promise<{
    exitCode: number;
    output: ContainerLogs;
  }> {
    const args = ['exec'];
    
    if (options?.user) args.push('--user', options.user);
    if (options?.workingDir) args.push('--workdir', options.workingDir);
    if (options?.environment) {
      Object.entries(options.environment).forEach(([key, value]) => {
        args.push('--env', `${key}=${value}`);
      });
    }
    
    args.push(containerId);
    args.push(...command);

    try {
      const result = await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      
      const logs: ContainerLogs = {
        stdout: result.stdout,
        stderr: result.stderr,
        combined: result.stdout + result.stderr,
        timestamp: new Date()
      };

      return {
        exitCode: 0,
        output: logs
      };
    } catch (error: any) {
      const logs: ContainerLogs = {
        stdout: error.stdout || '',
        stderr: error.stderr || error.message,
        combined: (error.stdout || '') + (error.stderr || error.message),
        timestamp: new Date()
      };

      return {
        exitCode: error.code || 1,
        output: logs
      };
    }
  }

  async getContainerStatus(containerId: string): Promise<ContainerStatus> {
    try {
      const result = await execAsync(`${this.podmanPath} inspect ${containerId} --format json`);
      const containerInfo = JSON.parse(result.stdout)[0];

      return {
        id: containerInfo.Id,
        name: containerInfo.Name,
        state: this.mapPodmanState(containerInfo.State.Status),
        status: containerInfo.State.Status,
        image: containerInfo.Config.Image,
        createdAt: new Date(containerInfo.Created),
        startedAt: containerInfo.State.StartedAt ? new Date(containerInfo.State.StartedAt) : undefined,
        finishedAt: containerInfo.State.FinishedAt ? new Date(containerInfo.State.FinishedAt) : undefined,
        exitCode: containerInfo.State.ExitCode,
        health: containerInfo.State.Health?.Status || 'none'
      };
    } catch (error: any) {
      throw new Error(`Failed to get container status: ${error.message}`);
    }
  }

  async listContainers(filters?: Record<string, string>): Promise<ContainerStatus[]> {
    try {
      const args = ['ps', '--all', '--format', 'json'];
      
      if (filters) {
        Object.entries(filters).forEach(([key, value]) => {
          args.push('--filter', `${key}=${value}`);
        });
      }

      const result = await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      const containers = JSON.parse(result.stdout);

      return containers.map((container: any) => ({
        id: container.Id,
        name: container.Names[0],
        state: this.mapPodmanState(container.State),
        status: container.Status,
        image: container.Image,
        createdAt: new Date(container.CreatedAt * 1000),
        ports: container.Ports ? this.parsePorts(container.Ports) : undefined
      }));
    } catch (error: any) {
      throw new Error(`Failed to list containers: ${error.message}`);
    }
  }

  async getContainerLogs(
    containerId: string,
    options?: { tail?: number; since?: Date; follow?: boolean }
  ): Promise<ContainerLogs | AsyncIterable<string>> {
    const args = ['logs'];
    
    if (options?.tail) args.push('--tail', options.tail.toString());
    if (options?.since) args.push('--since', options.since.toISOString());
    if (options?.follow) args.push('--follow');
    
    args.push(containerId);

    if (options?.follow) {
      // Return async iterable for streaming logs
      return this.streamLogs(args);
    } else {
      try {
        const result = await execAsync(`${this.podmanPath} ${args.join(' ')}`);
        
        return {
          stdout: result.stdout,
          stderr: result.stderr,
          combined: result.stdout + result.stderr,
          timestamp: new Date()
        };
      } catch (error: any) {
        throw new Error(`Failed to get container logs: ${error.message}`);
      }
    }
  }

  private async *streamLogs(args: string[]): AsyncIterable<string> {
    const child = spawn(this.podmanPath, args);
    
    const streamData = async function* (stream: NodeJS.ReadableStream): AsyncIterable<string> {
      stream.setEncoding('utf8');
      for await (const chunk of stream) {
        yield chunk.toString();
      }
    };

    // Merge stdout and stderr streams
    const streams = [
      streamData(child.stdout),
      streamData(child.stderr)
    ];

    for await (const stream of streams) {
      for await (const chunk of stream) {
        yield chunk;
      }
    }
  }

  async getContainerStats(containerId: string): Promise<ContainerStats> {
    try {
      const result = await execAsync(`${this.podmanPath} stats ${containerId} --no-stream --format json`);
      const stats = JSON.parse(result.stdout);

      return {
        cpu: {
          usage: parseFloat(stats.CPUPerc.replace('%', '')),
          systemUsage: 0 // Not available in Podman stats
        },
        memory: {
          usage: this.parseSize(stats.MemUsage.split('/')[0]),
          limit: this.parseSize(stats.MemUsage.split('/')[1]),
          percentage: parseFloat(stats.MemPerc.replace('%', ''))
        },
        network: {
          rx: this.parseSize(stats.NetIO.split('/')[0]),
          tx: this.parseSize(stats.NetIO.split('/')[1])
        },
        io: {
          read: this.parseSize(stats.BlockIO.split('/')[0]),
          write: this.parseSize(stats.BlockIO.split('/')[1])
        },
        timestamp: new Date()
      };
    } catch (error: any) {
      throw new Error(`Failed to get container stats: ${error.message}`);
    }
  }

  async buildImage(buildContext: ImageBuildContext, imageTag: string): Promise<string> {
    const args = ['build'];
    
    if (buildContext.dockerfilePath) {
      args.push('-f', path.resolve(buildContext.contextPath, buildContext.dockerfilePath));
    }
    
    if (buildContext.target) args.push('--target', buildContext.target);
    
    if (buildContext.buildArgs) {
      Object.entries(buildContext.buildArgs).forEach(([key, value]) => {
        args.push('--build-arg', `${key}=${value}`);
      });
    }
    
    if (buildContext.labels) {
      Object.entries(buildContext.labels).forEach(([key, value]) => {
        args.push('--label', `${key}=${value}`);
      });
    }
    
    if (!buildContext.cache) args.push('--no-cache');
    if (buildContext.pullBaseImage) args.push('--pull');
    
    args.push('-t', imageTag);
    args.push(buildContext.contextPath);

    try {
      const result = await execAsync(`${this.podmanPath} ${args.join(' ')}`, {
        timeout: 600000, // 10 minutes timeout for builds
        maxBuffer: 50 * 1024 * 1024 // 50MB buffer
      });

      // Extract image ID from build output
      const imageIdMatch = result.stdout.match(/Successfully tagged .+ ([a-f0-9]{12})/);
      const imageId = imageIdMatch ? imageIdMatch[1] : imageTag;

      this.emit('imageBuild', {
        imageTag,
        imageId,
        buildContext
      });

      return imageId;
    } catch (error: any) {
      this.emit('error', {
        operation: 'buildImage',
        error: error.message,
        imageTag,
        buildContext
      });
      throw new Error(`Failed to build image: ${error.message}`);
    }
  }

  async pullImage(image: string, tag: string = 'latest'): Promise<void> {
    try {
      const fullImage = `${image}:${tag}`;
      await execAsync(`${this.podmanPath} pull ${fullImage}`);
      
      this.emit('imagePulled', { image: fullImage });
    } catch (error: any) {
      this.emit('error', {
        operation: 'pullImage',
        error: error.message,
        image: `${image}:${tag}`
      });
      throw new Error(`Failed to pull image: ${error.message}`);
    }
  }

  async pushImage(image: string, tag: string = 'latest'): Promise<void> {
    try {
      const fullImage = `${image}:${tag}`;
      await execAsync(`${this.podmanPath} push ${fullImage}`);
      
      this.emit('imagePushed', { image: fullImage });
    } catch (error: any) {
      this.emit('error', {
        operation: 'pushImage',
        error: error.message,
        image: `${image}:${tag}`
      });
      throw new Error(`Failed to push image: ${error.message}`);
    }
  }

  async removeImage(image: string, force: boolean = false): Promise<void> {
    try {
      const args = ['rmi'];
      if (force) args.push('--force');
      args.push(image);

      await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      
      this.emit('imageRemoved', { image, force });
    } catch (error: any) {
      this.emit('error', {
        operation: 'removeImage',
        error: error.message,
        image
      });
      throw new Error(`Failed to remove image: ${error.message}`);
    }
  }

  async listImages(filters?: Record<string, string>): Promise<ImageInfo[]> {
    try {
      const args = ['images', '--format', 'json'];
      
      if (filters) {
        Object.entries(filters).forEach(([key, value]) => {
          args.push('--filter', `${key}=${value}`);
        });
      }

      const result = await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      const images = JSON.parse(result.stdout);

      return images.map((image: any) => ({
        id: image.Id,
        repository: image.Repository,
        tag: image.Tag,
        digest: image.Digest,
        size: image.Size,
        created: new Date(image.Created * 1000),
        labels: image.Labels
      }));
    } catch (error: any) {
      throw new Error(`Failed to list images: ${error.message}`);
    }
  }

  async tagImage(sourceImage: string, targetImage: string): Promise<void> {
    try {
      await execAsync(`${this.podmanPath} tag ${sourceImage} ${targetImage}`);
      
      this.emit('imageTagged', { sourceImage, targetImage });
    } catch (error: any) {
      this.emit('error', {
        operation: 'tagImage',
        error: error.message,
        sourceImage,
        targetImage
      });
      throw new Error(`Failed to tag image: ${error.message}`);
    }
  }

  // Volume management
  async createVolume(name: string, labels?: Record<string, string>): Promise<void> {
    try {
      const args = ['volume', 'create'];
      
      if (labels) {
        Object.entries(labels).forEach(([key, value]) => {
          args.push('--label', `${key}=${value}`);
        });
      }
      
      args.push(name);

      await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      
      this.emit('volumeCreated', { name, labels });
    } catch (error: any) {
      this.emit('error', {
        operation: 'createVolume',
        error: error.message,
        name
      });
      throw new Error(`Failed to create volume: ${error.message}`);
    }
  }

  async removeVolume(name: string, force: boolean = false): Promise<void> {
    try {
      const args = ['volume', 'rm'];
      if (force) args.push('--force');
      args.push(name);

      await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      
      this.emit('volumeRemoved', { name, force });
    } catch (error: any) {
      this.emit('error', {
        operation: 'removeVolume',
        error: error.message,
        name
      });
      throw new Error(`Failed to remove volume: ${error.message}`);
    }
  }

  async listVolumes(): Promise<Array<{
    name: string;
    driver: string;
    mountpoint: string;
    labels?: Record<string, string>;
    size?: number;
  }>> {
    try {
      const result = await execAsync(`${this.podmanPath} volume ls --format json`);
      const volumes = JSON.parse(result.stdout);

      return volumes.map((volume: any) => ({
        name: volume.Name,
        driver: volume.Driver,
        mountpoint: volume.Mountpoint,
        labels: volume.Labels,
        size: volume.Size
      }));
    } catch (error: any) {
      throw new Error(`Failed to list volumes: ${error.message}`);
    }
  }

  // Network management
  async createNetwork(
    name: string,
    options?: { driver?: string; subnet?: string; gateway?: string; labels?: Record<string, string> }
  ): Promise<void> {
    try {
      const args = ['network', 'create'];
      
      if (options?.driver) args.push('--driver', options.driver);
      if (options?.subnet) args.push('--subnet', options.subnet);
      if (options?.gateway) args.push('--gateway', options.gateway);
      
      if (options?.labels) {
        Object.entries(options.labels).forEach(([key, value]) => {
          args.push('--label', `${key}=${value}`);
        });
      }
      
      args.push(name);

      await execAsync(`${this.podmanPath} ${args.join(' ')}`);
      
      this.emit('networkCreated', { name, options });
    } catch (error: any) {
      this.emit('error', {
        operation: 'createNetwork',
        error: error.message,
        name
      });
      throw new Error(`Failed to create network: ${error.message}`);
    }
  }

  async removeNetwork(name: string): Promise<void> {
    try {
      await execAsync(`${this.podmanPath} network rm ${name}`);
      
      this.emit('networkRemoved', { name });
    } catch (error: any) {
      this.emit('error', {
        operation: 'removeNetwork',
        error: error.message,
        name
      });
      throw new Error(`Failed to remove network: ${error.message}`);
    }
  }

  async listNetworks(): Promise<Array<{
    id: string;
    name: string;
    driver: string;
    subnet?: string;
    gateway?: string;
    labels?: Record<string, string>;
  }>> {
    try {
      const result = await execAsync(`${this.podmanPath} network ls --format json`);
      const networks = JSON.parse(result.stdout);

      return networks.map((network: any) => ({
        id: network.NetworkID,
        name: network.Name,
        driver: network.Driver,
        labels: network.Labels
      }));
    } catch (error: any) {
      throw new Error(`Failed to list networks: ${error.message}`);
    }
  }

  // Compose operations
  supportsCompose(): boolean {
    return this.engineInfo.capabilities.compose;
  }

  async runCompose(
    composeFile: string,
    options?: { projectName?: string; environment?: Record<string, string>; detached?: boolean }
  ): Promise<void> {
    if (!this.supportsCompose()) {
      throw new Error('Compose is not available for this Podman installation');
    }

    try {
      const args = ['-f', composeFile];
      
      if (options?.projectName) {
        args.unshift('-p', options.projectName);
      }
      
      args.push('up');
      
      if (options?.detached !== false) args.push('-d');

      const env = { ...process.env, ...options?.environment };
      await execAsync(`${this.composePath} ${args.join(' ')}`, { env });
      
      this.emit('composeUp', { composeFile, options });
    } catch (error: any) {
      this.emit('error', {
        operation: 'runCompose',
        error: error.message,
        composeFile
      });
      throw new Error(`Failed to run compose: ${error.message}`);
    }
  }

  async stopCompose(composeFile: string, projectName?: string): Promise<void> {
    if (!this.supportsCompose()) {
      throw new Error('Compose is not available for this Podman installation');
    }

    try {
      const args = ['-f', composeFile];
      
      if (projectName) {
        args.unshift('-p', projectName);
      }
      
      args.push('down');

      await execAsync(`${this.composePath} ${args.join(' ')}`);
      
      this.emit('composeDown', { composeFile, projectName });
    } catch (error: any) {
      this.emit('error', {
        operation: 'stopCompose',
        error: error.message,
        composeFile
      });
      throw new Error(`Failed to stop compose: ${error.message}`);
    }
  }

  // Cleanup and maintenance
  async cleanup(options?: {
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
  }> {
    const results = {
      containers: 0,
      images: 0,
      volumes: 0,
      networks: 0,
      spaceSaved: 0
    };

    try {
      if (options?.containers !== false) {
        const containerResult = await execAsync(`${this.podmanPath} container prune ${options?.force ? '--force' : ''} --format json`);
        const containerData = JSON.parse(containerResult.stdout);
        results.containers = containerData.ContainersDeleted?.length || 0;
        results.spaceSaved += containerData.SpaceReclaimed || 0;
      }

      if (options?.images !== false) {
        const imageResult = await execAsync(`${this.podmanPath} image prune ${options?.force ? '--force' : ''} --format json`);
        const imageData = JSON.parse(imageResult.stdout);
        results.images = imageData.ImagesDeleted?.length || 0;
        results.spaceSaved += imageData.SpaceReclaimed || 0;
      }

      if (options?.volumes !== false) {
        const volumeResult = await execAsync(`${this.podmanPath} volume prune ${options?.force ? '--force' : ''} --format json`);
        const volumeData = JSON.parse(volumeResult.stdout);
        results.volumes = volumeData.VolumesDeleted?.length || 0;
        results.spaceSaved += volumeData.SpaceReclaimed || 0;
      }

      if (options?.networks !== false) {
        const networkResult = await execAsync(`${this.podmanPath} network prune ${options?.force ? '--force' : ''} --format json`);
        const networkData = JSON.parse(networkResult.stdout);
        results.networks = networkData.NetworksDeleted?.length || 0;
      }

      this.emit('cleanup', results);
      return results;
    } catch (error: any) {
      this.emit('error', {
        operation: 'cleanup',
        error: error.message,
        options
      });
      throw new Error(`Failed to cleanup: ${error.message}`);
    }
  }

  // Helper methods
  private mapPodmanState(state: string): ContainerStatus['state'] {
    const stateMap: Record<string, ContainerStatus['state']> = {
      'created': 'created',
      'running': 'running',
      'paused': 'paused',
      'restarting': 'restarting',
      'removing': 'removing',
      'exited': 'exited',
      'dead': 'dead',
      'configured': 'created'
    };

    return stateMap[state.toLowerCase()] || 'exited';
  }

  private parsePorts(portsString: string): any[] {
    // Parse Podman port format: "0.0.0.0:8080->80/tcp, 0.0.0.0:8443->443/tcp"
    if (!portsString) return [];

    return portsString.split(', ').map(portMapping => {
      const match = portMapping.match(/(.+?):(\d+)->(\d+)\/(.+)/);
      if (match) {
        return {
          hostIp: match[1],
          hostPort: parseInt(match[2]),
          containerPort: parseInt(match[3]),
          protocol: match[4]
        };
      }
      return null;
    }).filter(Boolean);
  }

  private parseSize(sizeStr: string): number {
    const units: Record<string, number> = {
      'B': 1,
      'kB': 1000,
      'MB': 1000000,
      'GB': 1000000000,
      'TB': 1000000000000,
      'KiB': 1024,
      'MiB': 1024 ** 2,
      'GiB': 1024 ** 3,
      'TiB': 1024 ** 4
    };

    const match = sizeStr.trim().match(/^(\d+(?:\.\d+)?)\s*([A-Za-z]+)$/);
    if (!match) return 0;

    const value = parseFloat(match[1]);
    const unit = match[2];
    const multiplier = units[unit] || 1;

    return Math.round(value * multiplier);
  }
}