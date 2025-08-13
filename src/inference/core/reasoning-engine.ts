/**
 * Core Reasoning Engine for ae-framework
 * Orchestrates different reasoning strategies and manages inference processes
 */

import { EventEmitter } from 'events';
import { SequentialStrategy } from '../strategies/sequential-strategy.js';
import { ParallelStrategy } from '../strategies/parallel-strategy.js';
import type { ReasoningContext, StrategyResult } from '../strategies/sequential-strategy.js';

export type ReasoningMode = 'sequential' | 'parallel' | 'adaptive' | 'hybrid';

export interface ReasoningRequest {
  id: string;
  mode: ReasoningMode;
  context: ReasoningContext;
  timeout?: number;
  priority?: 'low' | 'medium' | 'high' | 'critical';
  options?: {
    maxRetries?: number;
    fallbackMode?: ReasoningMode;
    validateResults?: boolean;
    cacheResults?: boolean;
  };
}

export interface ReasoningSession {
  id: string;
  startTime: Date;
  endTime?: Date;
  status: 'pending' | 'running' | 'completed' | 'failed' | 'timeout';
  request: ReasoningRequest;
  result?: StrategyResult;
  error?: Error;
  metrics: {
    duration: number;
    memoryUsed: number;
    strategySwitches: number;
    cacheHits: number;
  };
}

export interface EngineMetrics {
  totalRequests: number;
  successfulRequests: number;
  failedRequests: number;
  averageProcessingTime: number;
  averageConfidence: number;
  strategyUsage: Record<ReasoningMode, number>;
  memoryUsage: {
    current: number;
    peak: number;
    average: number;
  };
  cacheStatistics: {
    size: number;
    hitRate: number;
    evictions: number;
  };
}

export class ReasoningEngine extends EventEmitter {
  private sequentialStrategy: SequentialStrategy;
  private parallelStrategy: ParallelStrategy;
  private activeSessions = new Map<string, ReasoningSession>();
  private resultCache = new Map<string, { result: StrategyResult; timestamp: Date }>();
  private metrics: EngineMetrics;

  constructor(private options: {
    maxConcurrentSessions?: number;
    defaultTimeout?: number;
    cacheSize?: number;
    cacheTTL?: number;
    enableMetrics?: boolean;
  } = {}) {
    super();

    this.options = {
      maxConcurrentSessions: 10,
      defaultTimeout: 300000, // 5 minutes
      cacheSize: 100,
      cacheTTL: 3600000, // 1 hour
      enableMetrics: true,
      ...options
    };

    this.sequentialStrategy = new SequentialStrategy();
    this.parallelStrategy = new ParallelStrategy();
    
    this.metrics = this.initializeMetrics();

    // Set up periodic cleanup
    setInterval(() => this.performMaintenance(), 60000); // Every minute
  }

  /**
   * Process a reasoning request
   */
  async processRequest(request: ReasoningRequest): Promise<StrategyResult> {
    // Check cache first
    if (request.options?.cacheResults !== false) {
      const cached = this.getCachedResult(request);
      if (cached) {
        this.updateMetrics('cache_hit');
        return cached;
      }
    }

    // Validate request
    this.validateRequest(request);

    // Check session limits
    if (this.activeSessions.size >= this.options.maxConcurrentSessions!) {
      throw new Error('Maximum concurrent sessions reached');
    }

    // Create session
    const session = this.createSession(request);
    this.activeSessions.set(session.id, session);
    
    try {
      this.emit('sessionStart', session);
      session.status = 'running';

      // Execute reasoning strategy
      let result = await this.executeStrategy(request, session);

      // Validate results if requested
      if (request.options?.validateResults) {
        result = await this.validateResult(result, request);
      }

      // Update session
      session.result = result;
      session.status = 'completed';
      session.endTime = new Date();
      session.metrics.duration = session.endTime.getTime() - session.startTime.getTime();

      // Cache result if enabled
      if (request.options?.cacheResults !== false) {
        this.cacheResult(request, result);
      }

      this.updateMetrics('success', session);
      this.emit('sessionComplete', session);

      return result;

    } catch (error) {
      session.status = 'failed';
      session.error = error as Error;
      session.endTime = new Date();
      session.metrics.duration = session.endTime.getTime() - session.startTime.getTime();

      this.updateMetrics('failure', session);
      this.emit('sessionError', { session, error });

      // Try fallback strategy if configured
      if (request.options?.fallbackMode && request.options.fallbackMode !== request.mode) {
        try {
          const fallbackRequest = { ...request, mode: request.options.fallbackMode };
          session.metrics.strategySwitches++;
          return await this.executeStrategy(fallbackRequest, session);
        } catch (fallbackError) {
          throw error; // Throw original error
        }
      }

      throw error;

    } finally {
      this.activeSessions.delete(session.id);
    }
  }

  /**
   * Get current engine metrics
   */
  getMetrics(): EngineMetrics {
    return { ...this.metrics };
  }

  /**
   * Clear all caches and reset metrics
   */
  reset(): void {
    this.resultCache.clear();
    this.metrics = this.initializeMetrics();
    this.emit('engineReset');
  }

  /**
   * Register custom reasoning strategies
   */
  registerStrategy(mode: string, strategy: SequentialStrategy | ParallelStrategy): void {
    // For extensibility - could be implemented to support custom strategies
    this.emit('strategyRegistered', { mode, strategy });
  }

  private validateRequest(request: ReasoningRequest): void {
    if (!request.id) {
      throw new Error('Request ID is required');
    }

    if (!request.context) {
      throw new Error('Reasoning context is required');
    }

    if (!request.context.domain) {
      throw new Error('Context domain is required');
    }

    if (!['sequential', 'parallel', 'adaptive', 'hybrid'].includes(request.mode)) {
      throw new Error(`Invalid reasoning mode: ${request.mode}`);
    }
  }

  private createSession(request: ReasoningRequest): ReasoningSession {
    return {
      id: `session-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`,
      startTime: new Date(),
      status: 'pending',
      request,
      metrics: {
        duration: 0,
        memoryUsed: 0,
        strategySwitches: 0,
        cacheHits: 0
      }
    };
  }

  private async executeStrategy(request: ReasoningRequest, session: ReasoningSession): Promise<StrategyResult> {
    const timeout = request.timeout || this.options.defaultTimeout!;
    
    // Create timeout promise
    const timeoutPromise = new Promise<never>((_, reject) => {
      setTimeout(() => reject(new Error('Reasoning timeout')), timeout);
    });

    // Execute strategy based on mode
    const strategyPromise = this.selectAndExecuteStrategy(request, session);

    try {
      return await Promise.race([strategyPromise, timeoutPromise]);
    } catch (error) {
      if ((error as Error).message === 'Reasoning timeout') {
        session.status = 'timeout';
      }
      throw error;
    }
  }

  private async selectAndExecuteStrategy(request: ReasoningRequest, session: ReasoningSession): Promise<StrategyResult> {
    const startMemory = this.getCurrentMemoryUsage();

    let result: StrategyResult;

    switch (request.mode) {
      case 'sequential':
        result = await this.sequentialStrategy.execute(request.context);
        break;

      case 'parallel':
        result = await this.parallelStrategy.execute(request.context);
        break;

      case 'adaptive':
        result = await this.executeAdaptiveStrategy(request.context);
        break;

      case 'hybrid':
        result = await this.executeHybridStrategy(request.context);
        break;

      default:
        throw new Error(`Unsupported reasoning mode: ${request.mode}`);
    }

    session.metrics.memoryUsed = this.getCurrentMemoryUsage() - startMemory;
    return result;
  }

  private async executeAdaptiveStrategy(context: ReasoningContext): Promise<StrategyResult> {
    // Analyze context to choose best strategy
    const complexity = this.analyzeComplexity(context);
    const dataSize = this.estimateDataSize(context);
    const hasParallelizableWork = this.hasParallelizableWork(context);

    if (hasParallelizableWork && dataSize > 1000) {
      return this.parallelStrategy.execute(context);
    } else {
      return this.sequentialStrategy.execute(context);
    }
  }

  private async executeHybridStrategy(context: ReasoningContext): Promise<StrategyResult> {
    // Use both strategies and combine results
    const [sequentialResult, parallelResult] = await Promise.allSettled([
      this.sequentialStrategy.execute(context),
      this.parallelStrategy.execute(context)
    ]);

    if (sequentialResult.status === 'fulfilled' && parallelResult.status === 'fulfilled') {
      // Combine results
      return this.combineResults(sequentialResult.value, parallelResult.value);
    } else if (sequentialResult.status === 'fulfilled') {
      return sequentialResult.value;
    } else if (parallelResult.status === 'fulfilled') {
      return parallelResult.value;
    } else {
      throw new Error('Both strategies failed in hybrid mode');
    }
  }

  private combineResults(sequential: StrategyResult, parallel: StrategyResult): StrategyResult {
    // Simple combination - could be more sophisticated
    const combinedSteps = [...sequential.steps, ...parallel.steps];
    const avgConfidence = (sequential.confidence + parallel.confidence) / 2;
    
    return {
      success: sequential.success && parallel.success,
      steps: combinedSteps,
      finalConclusion: {
        sequential: sequential.finalConclusion,
        parallel: parallel.finalConclusion,
        combined: true
      },
      confidence: avgConfidence,
      reasoning: [
        ...sequential.reasoning,
        '--- Parallel Results ---',
        ...parallel.reasoning
      ]
    };
  }

  private async validateResult(result: StrategyResult, request: ReasoningRequest): Promise<StrategyResult> {
    // Basic result validation
    if (!result.success) {
      return result; // Don't modify failed results
    }

    if (result.confidence < 0.5) {
      result.reasoning.push('Warning: Low confidence result');
    }

    if (result.steps.length === 0) {
      throw new Error('Invalid result: No reasoning steps found');
    }

    return result;
  }

  private getCachedResult(request: ReasoningRequest): StrategyResult | null {
    const cacheKey = this.generateCacheKey(request);
    const cached = this.resultCache.get(cacheKey);
    
    if (!cached) return null;

    // Check TTL
    const age = Date.now() - cached.timestamp.getTime();
    if (age > this.options.cacheTTL!) {
      this.resultCache.delete(cacheKey);
      return null;
    }

    return cached.result;
  }

  private cacheResult(request: ReasoningRequest, result: StrategyResult): void {
    if (this.resultCache.size >= this.options.cacheSize!) {
      // Evict oldest entry
      const oldestKey = this.resultCache.keys().next().value;
      this.resultCache.delete(oldestKey);
      this.metrics.cacheStatistics.evictions++;
    }

    const cacheKey = this.generateCacheKey(request);
    this.resultCache.set(cacheKey, {
      result: { ...result },
      timestamp: new Date()
    });
  }

  private generateCacheKey(request: ReasoningRequest): string {
    // Generate a cache key based on request characteristics
    const contextHash = JSON.stringify({
      domain: request.context.domain,
      objectives: request.context.objectives,
      constraints: request.context.constraints
    });
    return `${request.mode}-${Buffer.from(contextHash).toString('base64').substr(0, 32)}`;
  }

  private analyzeComplexity(context: ReasoningContext): number {
    let complexity = 0;
    complexity += context.objectives.length * 2;
    complexity += context.constraints.length * 3;
    complexity += Object.keys(context.availableData).length;
    return complexity;
  }

  private estimateDataSize(context: ReasoningContext): number {
    return JSON.stringify(context.availableData).length;
  }

  private hasParallelizableWork(context: ReasoningContext): boolean {
    return Object.keys(context.availableData).length > 3 || context.objectives.length > 2;
  }

  private getCurrentMemoryUsage(): number {
    if (typeof process !== 'undefined' && process.memoryUsage) {
      return process.memoryUsage().heapUsed;
    }
    return 0;
  }

  private initializeMetrics(): EngineMetrics {
    return {
      totalRequests: 0,
      successfulRequests: 0,
      failedRequests: 0,
      averageProcessingTime: 0,
      averageConfidence: 0,
      strategyUsage: {
        sequential: 0,
        parallel: 0,
        adaptive: 0,
        hybrid: 0
      },
      memoryUsage: {
        current: 0,
        peak: 0,
        average: 0
      },
      cacheStatistics: {
        size: 0,
        hitRate: 0,
        evictions: 0
      }
    };
  }

  private updateMetrics(type: 'success' | 'failure' | 'cache_hit', session?: ReasoningSession): void {
    if (!this.options.enableMetrics) return;

    if (type === 'cache_hit') {
      this.metrics.cacheStatistics.hitRate = 
        (this.metrics.cacheStatistics.hitRate * this.metrics.totalRequests + 1) / 
        (this.metrics.totalRequests + 1);
      return;
    }

    this.metrics.totalRequests++;

    if (session) {
      if (type === 'success') {
        this.metrics.successfulRequests++;
        if (session.result) {
          this.metrics.averageConfidence = 
            (this.metrics.averageConfidence * (this.metrics.successfulRequests - 1) + session.result.confidence) / 
            this.metrics.successfulRequests;
        }
      } else {
        this.metrics.failedRequests++;
      }

      // Update processing time
      this.metrics.averageProcessingTime = 
        (this.metrics.averageProcessingTime * (this.metrics.totalRequests - 1) + session.metrics.duration) / 
        this.metrics.totalRequests;

      // Update strategy usage
      this.metrics.strategyUsage[session.request.mode]++;

      // Update memory metrics
      const currentMemory = this.getCurrentMemoryUsage();
      this.metrics.memoryUsage.current = currentMemory;
      this.metrics.memoryUsage.peak = Math.max(this.metrics.memoryUsage.peak, currentMemory);
      this.metrics.memoryUsage.average = 
        (this.metrics.memoryUsage.average * (this.metrics.totalRequests - 1) + currentMemory) / 
        this.metrics.totalRequests;
    }

    // Update cache statistics
    this.metrics.cacheStatistics.size = this.resultCache.size;
  }

  private performMaintenance(): void {
    // Clean expired cache entries
    const now = Date.now();
    for (const [key, cached] of this.resultCache.entries()) {
      if (now - cached.timestamp.getTime() > this.options.cacheTTL!) {
        this.resultCache.delete(key);
        this.metrics.cacheStatistics.evictions++;
      }
    }

    // Update cache size metric
    this.metrics.cacheStatistics.size = this.resultCache.size;

    this.emit('maintenanceComplete', {
      cacheSize: this.resultCache.size,
      activeSessions: this.activeSessions.size
    });
  }
}