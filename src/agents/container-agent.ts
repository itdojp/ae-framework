/**
 * Container Agent - Phase 3 of Issue #37
 * Integrates container-based verification environments with the ae-framework
 */

import { ContainerManager } from '../services/container/container-manager.js';
import type { ContainerManagerConfig, VerificationJob, VerificationEnvironment } from '../services/container/container-manager.js';
import { ContainerEngineFactory, type ContainerEngineName } from '../services/container/container-engine.js';
import * as path from 'path';
import * as fs from 'fs/promises';

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

export class ContainerAgent {
  private containerManager: ContainerManager;
  private config: ContainerAgentConfig;
  private initialized: boolean = false;

  constructor(config: ContainerAgentConfig = {}) {
    this.config = {
      containerfilesPath: path.join(process.cwd(), 'containers'),
      buildConfig: {
        parallel: true,
        maxConcurrentBuilds: 3,
        cacheEnabled: true
      },
      ...config
    };

    this.containerManager = new ContainerManager(config);
  }

  /**
   * Initialize the container agent and underlying systems
   */
  async initialize(): Promise<AgentResult> {
    try {
      if (this.initialized) {
        return {
          success: true,
          message: 'Container agent already initialized',
          data: { initialized: true }
        };
      }

      // Initialize container manager with timeout for CI environments
      const initTimeout = process.env['CI'] ? 10000 : 30000; // 10s for CI, 30s for local
      const initPromise = this.containerManager.initialize();
      
      let engineInfo;
      try {
        await Promise.race([
          initPromise,
          new Promise((_, reject) => 
            setTimeout(() => reject(new Error('Container engine initialization timeout')), initTimeout)
          )
        ]);
        engineInfo = this.containerManager.getEngineInfo();
      } catch (error: any) {
        // In CI environments, container engines might not be available
        // Continue with limited functionality
        if (process.env['CI'] || error.message.includes('not found') || error.message.includes('timeout')) {
          console.warn(`Container engine not available: ${error.message}`);
          console.warn('Running in degraded mode without container engine');
          engineInfo = { name: 'none', version: 'N/A', available: false };
        } else {
          throw error;
        }
      }

      // Check if Containerfiles directory exists and has container files
      try {
        await fs.access(this.config.containerfilesPath!);
        const files = await fs.readdir(this.config.containerfilesPath!);
        const containerFiles = files.filter(f => f.startsWith('Containerfile.'));
        
        if (containerFiles.length === 0) {
          console.warn('Containerfiles directory exists but is empty');
          console.warn('Creating default container configurations...');
          await this.createDefaultContainerfiles();
        }
      } catch {
        console.warn(`Containerfiles directory not found: ${this.config.containerfilesPath}`);
        console.warn('Creating default container configurations...');
        await this.createDefaultContainerfiles();
      }

      this.initialized = true;
      
      return {
        success: true,
        message: `Container agent initialized with ${engineInfo?.name || 'unknown'} engine`,
        data: {
          engine: engineInfo,
          containerfilesPath: this.config.containerfilesPath,
          initialized: true,
          degradedMode: engineInfo?.available === false
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to initialize container agent: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * Run verification job in container
   */
  async runVerification(request: ContainerVerificationRequest): Promise<AgentResult> {
    try {
      await this.ensureInitialized();

      // Validate project path exists
      try {
        await fs.access(request.projectPath);
      } catch {
        return {
          success: false,
          message: `Project path does not exist: ${request.projectPath}`,
          error: 'INVALID_PROJECT_PATH'
        };
      }

      // Build verification images if requested
      if (request.buildImages) {
        const buildResult = await this.buildVerificationImage({
          language: request.language,
          tools: request.tools
        });
        
        if (!buildResult.success) {
          return buildResult;
        }
      }

      // Create and run verification job
      const job = await this.containerManager.runVerificationJob({
        name: request.jobName || `${request.language}-verification-${Date.now()}`,
        projectPath: request.projectPath,
        language: request.language,
        tools: request.tools
      });

      return {
        success: job.status === 'completed',
        message: job.status === 'completed' 
          ? `Verification completed successfully`
          : `Verification ${job.status}${job.error ? ': ' + job.error : ''}`,
        data: {
          jobId: job.id,
          status: job.status,
          results: job.results,
          logs: job.logs,
          duration: job.endTime && job.startTime 
            ? job.endTime.getTime() - job.startTime.getTime()
            : null
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Container verification failed: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * Build verification container image
   */
  async buildVerificationImage(request: ContainerBuildRequest): Promise<AgentResult> {
    try {
      await this.ensureInitialized();

      const tag = request.tag || `ae-framework/verify-${request.language}:latest`;
      
      const imageId = await this.containerManager.buildVerificationImage(
        request.language,
        request.tools,
        {
          tag,
          ...(request.buildArgs ? { buildArgs: request.buildArgs } : {}),
          ...(request.push !== undefined ? { push: request.push } : {})
        }
      );

      return {
        success: true,
        message: `Successfully built verification image: ${tag}`,
        data: {
          imageId,
          tag,
          language: request.language,
          tools: request.tools,
          pushed: request.push || false
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to build verification image: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * Get verification job status
   */
  async getJobStatus(jobId: string): Promise<AgentResult> {
    try {
      await this.ensureInitialized();

      const job = this.containerManager.getJob(jobId);
      if (!job) {
        return {
          success: false,
          message: `Job not found: ${jobId}`,
          error: 'JOB_NOT_FOUND'
        };
      }

      return {
        success: true,
        message: `Job status: ${job.status}`,
        data: {
          id: job.id,
          name: job.name,
          status: job.status,
          language: job.language,
          tools: job.tools,
          startTime: job.startTime,
          endTime: job.endTime,
          results: job.results,
          error: job.error,
          logs: job.logs
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to get job status: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * List verification jobs
   */
  async listJobs(filter?: { status?: 'pending' | 'running' | 'completed' | 'failed'; language?: string }): Promise<AgentResult> {
    try {
      await this.ensureInitialized();

      const jobs = this.containerManager.listJobs(filter);

      return {
        success: true,
        message: `Found ${jobs.length} jobs`,
        data: {
          jobs: jobs.map(job => ({
            id: job.id,
            name: job.name,
            status: job.status,
            language: job.language,
            tools: job.tools,
            startTime: job.startTime,
            endTime: job.endTime,
            error: job.error
          })),
          total: jobs.length,
          filter
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to list jobs: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * Cancel running verification job
   */
  async cancelJob(jobId: string): Promise<AgentResult> {
    try {
      await this.ensureInitialized();

      await this.containerManager.cancelJob(jobId);

      return {
        success: true,
        message: `Job cancelled: ${jobId}`,
        data: { jobId, cancelled: true }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to cancel job: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * Get container agent and system status
   */
  async getStatus(): Promise<AgentResult<ContainerStatusResult>> {
    try {
      await this.ensureInitialized();

      const healthStatus = await this.containerManager.getHealthStatus();
      
      return {
        success: true,
        message: `Container system ${healthStatus.healthy ? 'healthy' : 'unhealthy'}`,
        data: {
          engine: healthStatus.engine,
          jobs: {
            active: healthStatus.jobs.running,
            completed: healthStatus.jobs.completed,
            failed: healthStatus.jobs.failed,
            total: healthStatus.jobs.total
          },
          resources: {
            containers: healthStatus.resources.activeContainers,
            images: healthStatus.resources.images,
            volumes: healthStatus.resources.volumes
          },
          health: healthStatus.healthy
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to get status: ${error.message}`,
        error: error.message,
        data: {
          engine: { name: 'unknown', version: 'unknown', available: false },
          jobs: { active: 0, completed: 0, failed: 0, total: 0 },
          resources: { containers: 0, images: 0, volumes: 0 },
          health: false
        }
      };
    }
  }

  /**
   * Cleanup old containers and resources
   */
  async cleanup(options?: { maxAge?: number; keepCompleted?: number; force?: boolean }): Promise<AgentResult> {
    try {
      await this.ensureInitialized();

      const result = await this.containerManager.cleanup(options);

      return {
        success: true,
        message: `Cleanup completed: removed ${result.jobsRemoved} jobs, ${result.containersRemoved} containers`,
        data: {
          jobsRemoved: result.jobsRemoved,
          containersRemoved: result.containersRemoved,
          spaceSaved: result.spaceSaved,
          options
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Cleanup failed: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * List available container engines
   */
  async listEngines(): Promise<AgentResult> {
    try {
      const engines = await ContainerEngineFactory.detectAvailableEngines();

      return {
        success: true,
        message: `Found ${engines.length} available container engines`,
        data: {
          engines: engines.map(engine => ({
            name: engine.name,
            version: engine.version,
            available: engine.available,
            capabilities: engine.capabilities
          })),
          total: engines.length
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to list engines: ${error.message}`,
        error: error.message
      };
    }
  }

  /**
   * Shutdown container agent
   */
  async shutdown(): Promise<AgentResult> {
    try {
      if (this.initialized) {
        await this.containerManager.shutdown();
        this.initialized = false;
      }

      return {
        success: true,
        message: 'Container agent shutdown complete',
        data: { shutdown: true }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Failed to shutdown container agent: ${error.message}`,
        error: error.message
      };
    }
  }

  // Private methods

  private async ensureInitialized(): Promise<void> {
    if (!this.initialized) {
      const result = await this.initialize();
      if (!result.success) {
        throw new Error(result.message);
      }
    }
  }

  private async createDefaultContainerfiles(): Promise<void> {
    const containerfilesPath = this.config.containerfilesPath!;
    
    try {
      await fs.mkdir(containerfilesPath, { recursive: true });

      // Create Rust Containerfile
      const rustContainerfile = `# Rust Verification Environment
FROM rust:1.75-slim as base

# Install system dependencies
RUN apt-get update && apt-get install -y \\
    build-essential \\
    pkg-config \\
    libssl-dev \\
    curl \\
    git \\
    && rm -rf /var/lib/apt/lists/*

# Install Rust verification tools
RUN cargo install --version 0.1.259 prusti-cli || echo "Prusti install failed"
RUN cargo install --version 0.36.0 kani-verifier || echo "Kani install failed"

# Install Miri for undefined behavior detection
RUN rustup component add miri

# Set up workspace
WORKDIR /workspace
VOLUME ["/workspace", "/output"]

# Verification target
FROM base as verification
ENV RUST_BACKTRACE=1
ENV CARGO_HOME=/opt/cargo
ENV PATH="/opt/cargo/bin:$PATH"

# Default command
CMD ["cargo", "check"]
`;

      await fs.writeFile(path.join(containerfilesPath, 'Containerfile.rust'), rustContainerfile);

      // Create Elixir Containerfile
      const elixirContainerfile = `# Elixir Verification Environment
FROM elixir:1.15-alpine as base

# Install system dependencies
RUN apk add --no-cache \\
    build-base \\
    git \\
    curl

# Install Hex and Rebar
RUN mix local.hex --force && \\
    mix local.rebar --force

# Set up workspace
WORKDIR /workspace
VOLUME ["/workspace", "/output"]

# Verification target
FROM base as verification
ENV MIX_ENV=test
ENV ERL_CRASH_DUMP=/dev/null

# Default command
CMD ["mix", "compile"]
`;

      await fs.writeFile(path.join(containerfilesPath, 'Containerfile.elixir'), elixirContainerfile);

      // Create Multi-language Containerfile
      const multiContainerfile = `# Multi-language Verification Environment
FROM ubuntu:22.04 as base

# Install system dependencies
RUN apt-get update && apt-get install -y \\
    curl \\
    wget \\
    git \\
    build-essential \\
    pkg-config \\
    libssl-dev \\
    ca-certificates \\
    && rm -rf /var/lib/apt/lists/*

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:$PATH"

# Install Rust verification tools
RUN cargo install --version 0.1.259 prusti-cli || echo "Prusti install failed"
RUN cargo install --version 0.36.0 kani-verifier || echo "Kani install failed"
RUN rustup component add miri

# Install Elixir
RUN wget -O erlang.deb https://packages.erlang-solutions.com/erlang/debian/pool/esl-erlang_25.3.2.7-1~ubuntu~jammy_amd64.deb && \\
    dpkg -i erlang.deb || apt-get install -f -y && \\
    wget -O elixir.deb https://packages.erlang-solutions.com/erlang/debian/pool/elixir_1.15.7-1~ubuntu~jammy_all.deb && \\
    dpkg -i elixir.deb || apt-get install -f -y && \\
    rm erlang.deb elixir.deb

# Install Hex and Rebar for Elixir
RUN mix local.hex --force && \\
    mix local.rebar --force

# Set up workspace
WORKDIR /workspace
VOLUME ["/workspace", "/output"]

# Verification target
FROM base as verification
ENV RUST_BACKTRACE=1
ENV CARGO_HOME=/opt/cargo
ENV MIX_ENV=test
ENV ERL_CRASH_DUMP=/dev/null
ENV PATH="/opt/cargo/bin:/opt/elixir/bin:$PATH"

# Default command
CMD ["sh", "-c", "echo 'Multi-language verification environment ready'"]
`;

      await fs.writeFile(path.join(containerfilesPath, 'Containerfile.multi'), multiContainerfile);

      console.log(`✅ Created default Containerfiles in ${containerfilesPath}`);
    } catch (error: any) {
      console.warn(`Failed to create default Containerfiles: ${error.message}`);
      throw error;
    }
  }

  // Event handling for container manager events
  private setupEventHandlers(): void {
    this.containerManager.on('initialized', (data) => {
      console.log(`Container manager initialized with ${data.engine} v${data.version}`);
    });

    this.containerManager.on('jobStarted', (data) => {
      console.log(`Verification job started: ${data.jobId} (${data.name})`);
    });

    this.containerManager.on('jobCompleted', (data) => {
      console.log(`Verification job completed: ${data.jobId} with status ${data.status}`);
    });

    this.containerManager.on('jobFailed', (data) => {
      console.warn(`Verification job failed: ${data.jobId} - ${data.error}`);
    });

    this.containerManager.on('cleanupCompleted', (data) => {
      console.log(`Container cleanup completed: ${data.containersRemoved} containers, ${data.jobsRemoved} jobs removed`);
    });

    this.containerManager.on('error', (data) => {
      console.error(`Container manager error in ${data.operation}: ${data.error}`);
    });
  }
}
