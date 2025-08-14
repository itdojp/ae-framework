/**
 * Container Manager - Container Lifecycle Management
 * Phase 3 of Issue #37: Orchestrates container operations across different engines
 */

import { EventEmitter } from 'events';
import * as path from 'path';
import { 
  ContainerEngine, 
  ContainerEngineFactory, 
  ContainerConfig, 
  ContainerRunOptions, 
  ContainerStatus,
  ContainerLogs,
  ImageBuildContext,
  type ContainerEngineName 
} from './container-engine.js';

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

export class ContainerManager extends EventEmitter {
  private engine!: ContainerEngine;
  private config: ContainerManagerConfig;
  private activeJobs: Map<string, VerificationJob> = new Map();
  private healthChecks: Map<string, ContainerHealthCheck> = new Map();
  private cleanupTimer?: NodeJS.Timeout;
  private healthCheckTimer?: NodeJS.Timeout;

  constructor(config: ContainerManagerConfig = {}) {
    super();
    
    this.config = {
      autoCleanup: true,
      maxConcurrentContainers: 10,
      defaultTimeout: 300, // 5 minutes
      resourceLimits: {
        memory: '2g',
        cpus: '1.0'
      },
      securityDefaults: {
        rootless: true,
        readOnlyRootFilesystem: false,
        noNewPrivileges: true
      },
      ...config
    };
  }

  /**
   * Initialize the container manager
   */
  async initialize(): Promise<void> {
    try {
      // Create preferred engine or auto-detect with timeout for CI
      const createTimeout = process.env.CI ? 5000 : 15000; // 5s for CI, 15s for local
      
      const enginePromise = this.config.preferredEngine 
        ? ContainerEngineFactory.createEngine(this.config.preferredEngine)
        : ContainerEngineFactory.createPreferredEngine();
      
      this.engine = await Promise.race([
        enginePromise,
        new Promise<any>((_, reject) => 
          setTimeout(() => reject(new Error('Engine creation timeout')), createTimeout)
        )
      ]);

      // Verify engine is available with timeout
      const availabilityTimeout = process.env.CI ? 3000 : 10000; // 3s for CI, 10s for local
      const availabilityPromise = this.engine.checkAvailability();
      
      const isAvailable = await Promise.race([
        availabilityPromise,
        new Promise<boolean>((_, reject) => 
          setTimeout(() => reject(new Error('Availability check timeout')), availabilityTimeout)
        )
      ]);

      if (!isAvailable) {
        throw new Error(`Container engine ${this.engine.getName()} is not available`);
      }

      console.log(`🐋 Container Manager initialized with ${this.engine.getName()} ${this.engine.getVersion()}`);

      // Setup event listeners
      this.setupEngineEventListeners();

      // Start background services (only if not in CI)
      if (!process.env.CI) {
        this.startBackgroundServices();
      }

      this.emit('initialized', {
        engine: this.engine.getName(),
        version: this.engine.getVersion(),
        capabilities: this.engine.getCapabilities()
      });

    } catch (error: any) {
      this.emit('error', {
        operation: 'initialize',
        error: error.message
      });
      throw error;
    }
  }

  /**
   * Create a verification environment
   */
  async createVerificationEnvironment(env: VerificationEnvironment): Promise<string> {
    try {
      const config: ContainerConfig = {
        name: `ae-verify-${env.name}-${Date.now()}`,
        image: env.baseImage,
        environment: {
          AE_VERIFICATION_MODE: 'true',
          AE_LANGUAGE: env.language,
          AE_TOOLS: env.tools.join(','),
          ...env.environment
        },
        volumes: env.volumes,
        resources: env.resources,
        security: {
          ...this.config.securityDefaults,
          readOnlyRootFilesystem: false // Verification might need to write temp files
        },
        labels: {
          'ae-framework.type': 'verification',
          'ae-framework.language': env.language,
          'ae-framework.tools': env.tools.join(','),
          'ae-framework.created': new Date().toISOString()
        },
        autoRemove: this.config.autoCleanup,
        detached: true
      };

      const containerId = await this.engine.createContainer(config);
      
      this.emit('environmentCreated', {
        containerId,
        environment: env.name,
        language: env.language
      });

      return containerId;
    } catch (error: any) {
      this.emit('error', {
        operation: 'createVerificationEnvironment',
        error: error.message,
        environment: env.name
      });
      throw error;
    }
  }

  /**
   * Run verification job in container
   */
  async runVerificationJob(job: Omit<VerificationJob, 'id' | 'status' | 'startTime'>): Promise<VerificationJob> {
    const jobId = `verify-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
    
    const verificationJob: VerificationJob = {
      id: jobId,
      status: 'pending',
      startTime: new Date(),
      ...job
    };

    this.activeJobs.set(jobId, verificationJob);

    try {
      // Check concurrent job limit
      const runningJobs = Array.from(this.activeJobs.values()).filter(j => j.status === 'running').length;
      if (runningJobs >= this.config.maxConcurrentContainers!) {
        throw new Error(`Maximum concurrent containers limit reached (${this.config.maxConcurrentContainers})`);
      }

      // Get verification environment
      const environment = this.getVerificationEnvironment(job.language);
      
      // Create container configuration
      const config: ContainerConfig = {
        name: `ae-verify-${jobId}`,
        image: environment.baseImage,
        command: this.buildVerificationCommand(job),
        environment: {
          AE_PROJECT_PATH: '/workspace',
          AE_VERIFICATION_TOOLS: job.tools.join(','),
          AE_JOB_ID: jobId,
          ...environment.environment
        },
        volumes: [
          {
            source: path.resolve(job.projectPath),
            target: '/workspace',
            readonly: true
          },
          {
            source: `ae-verify-output-${jobId}`,
            target: '/output',
            type: 'volume'
          }
        ],
        resources: {
          ...this.config.resourceLimits,
          ...environment.resources
        },
        security: this.config.securityDefaults,
        labels: {
          'ae-framework.job-id': jobId,
          'ae-framework.type': 'verification-job',
          'ae-framework.language': job.language,
          'ae-framework.project': path.basename(job.projectPath)
        },
        autoRemove: this.config.autoCleanup,
        restart: 'no'
      };

      // Run the container
      verificationJob.status = 'running';
      this.activeJobs.set(jobId, verificationJob);

      this.emit('jobStarted', {
        jobId,
        name: job.name,
        language: job.language
      });

      const result = await this.engine.runContainer(config, {
        timeout: this.config.defaultTimeout,
        capture: true,
        cleanup: this.config.autoCleanup
      });

      // Update job with results
      verificationJob.status = result.exitCode === 0 ? 'completed' : 'failed';
      verificationJob.endTime = new Date();
      verificationJob.containerId = result.containerId;
      verificationJob.logs = result.output;
      verificationJob.results = await this.parseVerificationResults(result.output);

      if (result.exitCode !== 0) {
        verificationJob.error = `Verification failed with exit code ${result.exitCode}`;
      }

      this.activeJobs.set(jobId, verificationJob);

      this.emit('jobCompleted', {
        jobId,
        status: verificationJob.status,
        exitCode: result.exitCode,
        duration: verificationJob.endTime.getTime() - verificationJob.startTime!.getTime()
      });

      return verificationJob;

    } catch (error: any) {
      verificationJob.status = 'failed';
      verificationJob.endTime = new Date();
      verificationJob.error = error.message;
      
      this.activeJobs.set(jobId, verificationJob);

      this.emit('jobFailed', {
        jobId,
        error: error.message
      });

      throw error;
    }
  }

  /**
   * Get job status
   */
  getJob(jobId: string): VerificationJob | undefined {
    return this.activeJobs.get(jobId);
  }

  /**
   * List all jobs
   */
  listJobs(filter?: { status?: VerificationJob['status']; language?: string }): VerificationJob[] {
    let jobs = Array.from(this.activeJobs.values());

    if (filter) {
      if (filter.status) {
        jobs = jobs.filter(job => job.status === filter.status);
      }
      if (filter.language) {
        jobs = jobs.filter(job => job.language === filter.language);
      }
    }

    return jobs.sort((a, b) => (b.startTime?.getTime() || 0) - (a.startTime?.getTime() || 0));
  }

  /**
   * Cancel a running job
   */
  async cancelJob(jobId: string): Promise<void> {
    const job = this.activeJobs.get(jobId);
    if (!job) {
      throw new Error(`Job ${jobId} not found`);
    }

    if (job.status !== 'running') {
      throw new Error(`Job ${jobId} is not running (status: ${job.status})`);
    }

    try {
      if (job.containerId) {
        await this.engine.stopContainer(job.containerId, 10);
        await this.engine.removeContainer(job.containerId, true);
      }

      job.status = 'failed';
      job.endTime = new Date();
      job.error = 'Job cancelled by user';

      this.activeJobs.set(jobId, job);

      this.emit('jobCancelled', { jobId });
    } catch (error: any) {
      this.emit('error', {
        operation: 'cancelJob',
        error: error.message,
        jobId
      });
      throw error;
    }
  }

  /**
   * Build verification container image
   */
  async buildVerificationImage(
    language: 'rust' | 'elixir' | 'multi',
    tools: string[],
    options?: {
      tag?: string;
      buildArgs?: Record<string, string>;
      push?: boolean;
    }
  ): Promise<string> {
    const tag = options?.tag || `ae-framework/verify-${language}:latest`;
    
    try {
      const buildContext: ImageBuildContext = {
        contextPath: path.join(process.cwd(), 'containers'),
        dockerfilePath: `Containerfile.${language}`,
        target: 'verification',
        buildArgs: {
          VERIFICATION_TOOLS: tools.join(','),
          ...options?.buildArgs
        },
        labels: {
          'ae-framework.type': 'verification-image',
          'ae-framework.language': language,
          'ae-framework.tools': tools.join(','),
          'ae-framework.version': '1.0.0'
        },
        cache: true,
        pullBaseImage: true
      };

      const imageId = await this.engine.buildImage(buildContext, tag);

      if (options?.push) {
        await this.engine.pushImage(tag.split(':')[0], tag.split(':')[1]);
      }

      this.emit('imageBuilt', {
        tag,
        imageId,
        language,
        tools
      });

      return imageId;
    } catch (error: any) {
      this.emit('error', {
        operation: 'buildVerificationImage',
        error: error.message,
        language,
        tag
      });
      throw error;
    }
  }

  /**
   * Get container engine information
   */
  getEngineInfo() {
    return this.engine ? this.engine.getEngineInfo() : null;
  }

  /**
   * List available container engines
   */
  async listAvailableEngines() {
    return await ContainerEngineFactory.detectAvailableEngines();
  }

  /**
   * Get system health status
   */
  async getHealthStatus(): Promise<{
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
  }> {
    try {
      const engineInfo = this.engine.getEngineInfo();
      const containers = await this.engine.listContainers();
      const images = await this.engine.listImages();
      const volumes = await this.engine.listVolumes();

      const jobs = {
        total: this.activeJobs.size,
        running: Array.from(this.activeJobs.values()).filter(j => j.status === 'running').length,
        completed: Array.from(this.activeJobs.values()).filter(j => j.status === 'completed').length,
        failed: Array.from(this.activeJobs.values()).filter(j => j.status === 'failed').length
      };

      return {
        healthy: engineInfo.available && jobs.running < this.config.maxConcurrentContainers!,
        engine: {
          name: engineInfo.name,
          version: engineInfo.version,
          available: engineInfo.available
        },
        jobs,
        resources: {
          activeContainers: containers.length,
          images: images.length,
          volumes: volumes.length
        }
      };
    } catch (error: any) {
      return {
        healthy: false,
        engine: {
          name: 'unknown',
          version: 'unknown',
          available: false
        },
        jobs: { total: 0, running: 0, completed: 0, failed: 0 },
        resources: { activeContainers: 0, images: 0, volumes: 0 }
      };
    }
  }

  /**
   * Cleanup old jobs and containers
   */
  async cleanup(options?: {
    maxAge?: number; // seconds
    keepCompleted?: number;
    force?: boolean;
  }): Promise<{
    jobsRemoved: number;
    containersRemoved: number;
    spaceSaved: number;
  }> {
    const maxAge = options?.maxAge || 3600; // 1 hour default
    const keepCompleted = options?.keepCompleted || 10;
    const cutoffTime = Date.now() - (maxAge * 1000);

    let jobsRemoved = 0;
    let containersRemoved = 0;
    let spaceSaved = 0;

    try {
      // Cleanup old jobs
      const completedJobs = Array.from(this.activeJobs.values())
        .filter(job => job.status === 'completed' && job.endTime && job.endTime.getTime() < cutoffTime)
        .sort((a, b) => (b.endTime?.getTime() || 0) - (a.endTime?.getTime() || 0))
        .slice(keepCompleted); // Keep most recent

      for (const job of completedJobs) {
        this.activeJobs.delete(job.id);
        jobsRemoved++;
      }

      // Cleanup failed jobs older than cutoff
      const failedJobs = Array.from(this.activeJobs.values())
        .filter(job => job.status === 'failed' && job.endTime && job.endTime.getTime() < cutoffTime);

      for (const job of failedJobs) {
        this.activeJobs.delete(job.id);
        jobsRemoved++;
      }

      // Cleanup containers and images
      const engineCleanup = await this.engine.cleanup({
        containers: true,
        images: true,
        volumes: false, // Keep volumes for now
        networks: false,
        force: options?.force
      });

      containersRemoved = engineCleanup.containers;
      spaceSaved = engineCleanup.spaceSaved;

      this.emit('cleanupCompleted', {
        jobsRemoved,
        containersRemoved,
        spaceSaved
      });

      return { jobsRemoved, containersRemoved, spaceSaved };

    } catch (error: any) {
      this.emit('error', {
        operation: 'cleanup',
        error: error.message
      });
      throw error;
    }
  }

  /**
   * Shutdown the container manager
   */
  async shutdown(): Promise<void> {
    try {
      console.log('🛑 Shutting down Container Manager...');

      // Stop background services
      this.stopBackgroundServices();

      // Cancel running jobs
      const runningJobs = Array.from(this.activeJobs.values()).filter(job => job.status === 'running');
      for (const job of runningJobs) {
        try {
          await this.cancelJob(job.id);
        } catch (error) {
          console.warn(`Failed to cancel job ${job.id}:`, error);
        }
      }

      // Cleanup if enabled
      if (this.config.autoCleanup) {
        await this.cleanup({ force: true });
      }

      this.emit('shutdown');
      console.log('✅ Container Manager shutdown complete');

    } catch (error: any) {
      this.emit('error', {
        operation: 'shutdown',
        error: error.message
      });
      throw error;
    }
  }

  // Private methods
  private setupEngineEventListeners(): void {
    this.engine.on('containerCreated', (event) => {
      this.emit('containerEvent', { type: 'created', ...event });
    });

    this.engine.on('containerStarted', (event) => {
      this.emit('containerEvent', { type: 'started', ...event });
    });

    this.engine.on('containerStopped', (event) => {
      this.emit('containerEvent', { type: 'stopped', ...event });
    });

    this.engine.on('error', (event) => {
      this.emit('engineError', event);
    });
  }

  private startBackgroundServices(): void {
    // Cleanup timer
    if (this.config.autoCleanup) {
      this.cleanupTimer = setInterval(async () => {
        try {
          await this.cleanup();
        } catch (error) {
          console.warn('Cleanup failed:', error);
        }
      }, 300000); // Every 5 minutes
    }

    // Health check timer
    this.healthCheckTimer = setInterval(async () => {
      try {
        const health = await this.getHealthStatus();
        this.emit('healthCheck', health);
      } catch (error) {
        console.warn('Health check failed:', error);
      }
    }, 60000); // Every minute
  }

  private stopBackgroundServices(): void {
    if (this.cleanupTimer) {
      clearInterval(this.cleanupTimer);
      this.cleanupTimer = undefined;
    }

    if (this.healthCheckTimer) {
      clearInterval(this.healthCheckTimer);
      this.healthCheckTimer = undefined;
    }
  }

  private getVerificationEnvironment(language: 'rust' | 'elixir' | 'multi'): VerificationEnvironment {
    const environments: Record<string, VerificationEnvironment> = {
      rust: {
        name: 'rust-verification',
        language: 'rust',
        tools: ['cargo', 'rustc', 'prusti', 'kani', 'miri'],
        baseImage: 'ae-framework/verify-rust:latest',
        resources: {
          memory: '2g',
          cpus: '1.0'
        },
        volumes: [],
        environment: {
          RUST_BACKTRACE: '1',
          CARGO_HOME: '/opt/cargo',
          PATH: '/opt/cargo/bin:/usr/local/bin:/usr/bin:/bin'
        }
      },
      elixir: {
        name: 'elixir-verification',
        language: 'elixir',
        tools: ['elixir', 'mix', 'exunit'],
        baseImage: 'ae-framework/verify-elixir:latest',
        resources: {
          memory: '1g',
          cpus: '0.5'
        },
        volumes: [],
        environment: {
          MIX_ENV: 'test',
          ERL_CRASH_DUMP: '/dev/null'
        }
      },
      multi: {
        name: 'multi-language-verification',
        language: 'multi',
        tools: ['cargo', 'rustc', 'elixir', 'mix', 'prusti', 'kani', 'miri'],
        baseImage: 'ae-framework/verify-multi:latest',
        resources: {
          memory: '4g',
          cpus: '2.0'
        },
        volumes: [],
        environment: {
          RUST_BACKTRACE: '1',
          MIX_ENV: 'test',
          PATH: '/opt/cargo/bin:/opt/elixir/bin:/usr/local/bin:/usr/bin:/bin'
        }
      }
    };

    return environments[language] || environments.multi;
  }

  private buildVerificationCommand(job: Omit<VerificationJob, 'id' | 'status' | 'startTime'>): string[] {
    const commands: string[] = ['sh', '-c'];
    
    let script = '';
    
    // Setup workspace
    script += 'cd /workspace && ';
    
    // Language-specific verification commands
    switch (job.language) {
      case 'rust':
        script += this.buildRustVerificationScript(job.tools);
        break;
      case 'elixir':
        script += this.buildElixirVerificationScript(job.tools);
        break;
      case 'multi':
        script += this.buildMultiLanguageVerificationScript(job.tools);
        break;
    }
    
    // Save results
    script += ' && echo "Verification completed" > /output/status.txt';
    
    commands.push(script);
    return commands;
  }

  private buildRustVerificationScript(tools: string[]): string {
    let script = '';
    
    // Check for Cargo.toml
    script += 'if [ -f "Cargo.toml" ]; then ';
    
    // Run each verification tool
    if (tools.includes('cargo')) {
      script += 'cargo check > /output/cargo-check.log 2>&1; ';
      script += 'cargo test > /output/cargo-test.log 2>&1; ';
    }
    
    if (tools.includes('prusti')) {
      script += 'cargo prusti > /output/prusti.log 2>&1; ';
    }
    
    if (tools.includes('kani')) {
      script += 'cargo kani > /output/kani.log 2>&1; ';
    }
    
    if (tools.includes('miri')) {
      script += 'cargo miri test > /output/miri.log 2>&1; ';
    }
    
    script += 'else echo "No Cargo.toml found" > /output/error.log; exit 1; fi';
    
    return script;
  }

  private buildElixirVerificationScript(tools: string[]): string {
    let script = '';
    
    // Check for mix.exs
    script += 'if [ -f "mix.exs" ]; then ';
    
    // Run verification commands
    if (tools.includes('mix')) {
      script += 'mix compile > /output/mix-compile.log 2>&1; ';
      script += 'mix test > /output/mix-test.log 2>&1; ';
    }
    
    script += 'else echo "No mix.exs found" > /output/error.log; exit 1; fi';
    
    return script;
  }

  private buildMultiLanguageVerificationScript(tools: string[]): string {
    let script = '';
    
    // Check for Rust project
    script += 'if [ -f "Cargo.toml" ]; then ';
    script += this.buildRustVerificationScript(tools.filter(t => ['cargo', 'prusti', 'kani', 'miri'].includes(t)));
    script += 'fi; ';
    
    // Check for Elixir project
    script += 'if [ -f "mix.exs" ]; then ';
    script += this.buildElixirVerificationScript(tools.filter(t => ['mix', 'elixir'].includes(t)));
    script += 'fi; ';
    
    return script;
  }

  private async parseVerificationResults(logs: ContainerLogs): Promise<any> {
    try {
      // Parse verification results from container logs
      const results = {
        success: !logs.stderr || !logs.stderr.includes('error'),
        output: logs.combined,
        timestamp: logs.timestamp,
        summary: {
          tests: 0,
          passed: 0,
          failed: 0,
          warnings: 0
        }
      };

      // Parse test results (simplified)
      const testMatches = logs.combined.match(/(\d+) passed.*?(\d+) failed/);
      if (testMatches) {
        results.summary.passed = parseInt(testMatches[1]);
        results.summary.failed = parseInt(testMatches[2]);
        results.summary.tests = results.summary.passed + results.summary.failed;
      }

      return results;
    } catch (error) {
      return {
        success: false,
        error: 'Failed to parse verification results',
        output: logs.combined,
        timestamp: logs.timestamp
      };
    }
  }
}