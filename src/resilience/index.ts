/**
 * Comprehensive Resilience System
 * Exports all resilience patterns and utilities
 */

// Internal imports for ResilienceSystem
import {
  BackoffStrategy,
  CircuitBreaker,
  TokenBucketRateLimiter,
  ResilientHttpClient,
  CircuitState,
  type CircuitBreakerStats,
} from './backoff-strategies.js';
import { BulkheadManager, type BulkheadStats } from './bulkhead-isolation.js';
import { TimeoutManager, TimeoutWrapper, type TimeoutStats } from './timeout-patterns.js';

// Backoff and retry strategies
export {
  BackoffStrategy,
  CircuitBreaker,
  CircuitState,
  TokenBucketRateLimiter,
  ResilientHttpClient,
  type RetryOptions,
  type RetryResult,
  type CircuitBreakerOptions,
  type CircuitBreakerStats,
  type RateLimiterOptions,
  type ResilientHttpOptions,
} from './backoff-strategies.js';

// Bulkhead isolation
export {
  Bulkhead,
  BulkheadManager,
  type BulkheadOptions,
  type BulkheadStats,
} from './bulkhead-isolation.js';

// Timeout patterns
export {
  TimeoutWrapper,
  AdaptiveTimeout,
  HierarchicalTimeout,
  TimeoutManager,
  TimeoutError,
  type TimeoutOptions,
  type AdaptiveTimeoutOptions,
  type TimeoutStats,
} from './timeout-patterns.js';

/**
 * Comprehensive resilience configuration
 */
export interface ResilienceConfig {
  retry?: {
    enabled: boolean;
    maxRetries: number;
    baseDelayMs: number;
    maxDelayMs: number;
    jitterType: 'none' | 'full' | 'equal' | 'decorrelated';
    multiplier: number;
  };
  circuitBreaker?: {
    enabled: boolean;
    failureThreshold: number;
    recoveryTimeout: number;
    monitoringPeriod: number;
    expectedErrors?: string[];
  };
  rateLimiter?: {
    enabled: boolean;
    tokensPerInterval: number;
    interval: number;
    maxTokens: number;
  };
  bulkhead?: {
    enabled: boolean;
    maxConcurrent: number;
    maxQueued: number;
    timeoutMs: number;
  };
  timeout?: {
    enabled: boolean;
    timeoutMs: number;
    adaptive?: {
      enabled: boolean;
      baseTimeoutMs: number;
      maxTimeoutMs: number;
      minTimeoutMs: number;
      adaptationFactor: number;
      windowSize: number;
    };
  };
}

/**
 * Default resilience configuration
 */
export const DEFAULT_RESILIENCE_CONFIG: ResilienceConfig = {
  retry: {
    enabled: true,
    maxRetries: 3,
    baseDelayMs: 100,
    maxDelayMs: 30000,
    jitterType: 'full',
    multiplier: 2,
  },
  circuitBreaker: {
    enabled: true,
    failureThreshold: 5,
    recoveryTimeout: 60000,
    monitoringPeriod: 120000,
  },
  rateLimiter: {
    enabled: true,
    tokensPerInterval: 100,
    interval: 60000,
    maxTokens: 100,
  },
  bulkhead: {
    enabled: true,
    maxConcurrent: 10,
    maxQueued: 50,
    timeoutMs: 30000,
  },
  timeout: {
    enabled: true,
    timeoutMs: 30000,
    adaptive: {
      enabled: true,
      baseTimeoutMs: 5000,
      maxTimeoutMs: 60000,
      minTimeoutMs: 1000,
      adaptationFactor: 0.1,
      windowSize: 100,
    },
  },
};

/**
 * Comprehensive resilience system that combines all patterns
 */
export class ResilienceSystem {
  private backoffStrategy?: BackoffStrategy;
  private circuitBreaker?: CircuitBreaker;
  private rateLimiter?: TokenBucketRateLimiter;
  private bulkheadManager: BulkheadManager;
  private timeoutManager: TimeoutManager;
  private httpClient?: ResilientHttpClient;

  constructor(private config: ResilienceConfig = DEFAULT_RESILIENCE_CONFIG) {
    this.initialize();
  }

  /**
   * Initialize resilience components based on configuration
   */
  private initialize(): void {
    // Initialize backoff strategy
    if (this.config.retry?.enabled) {
      this.backoffStrategy = new BackoffStrategy({
        maxRetries: this.config.retry.maxRetries,
        baseDelayMs: this.config.retry.baseDelayMs,
        maxDelayMs: this.config.retry.maxDelayMs,
        jitterType: this.config.retry.jitterType,
        multiplier: this.config.retry.multiplier,
      });
    }

    // Initialize circuit breaker
    if (this.config.circuitBreaker?.enabled) {
      this.circuitBreaker = new CircuitBreaker({
        failureThreshold: this.config.circuitBreaker.failureThreshold,
        recoveryTimeout: this.config.circuitBreaker.recoveryTimeout,
        monitoringPeriod: this.config.circuitBreaker.monitoringPeriod,
        expectedErrors: this.config.circuitBreaker.expectedErrors,
      });
    }

    // Initialize rate limiter
    if (this.config.rateLimiter?.enabled) {
      this.rateLimiter = new TokenBucketRateLimiter({
        tokensPerInterval: this.config.rateLimiter.tokensPerInterval,
        interval: this.config.rateLimiter.interval,
        maxTokens: this.config.rateLimiter.maxTokens,
      });
    }

    // Initialize managers
    this.bulkheadManager = new BulkheadManager();
    this.timeoutManager = new TimeoutManager();

    // Initialize HTTP client with all patterns
    this.httpClient = new ResilientHttpClient({
      retryOptions: this.config.retry?.enabled ? {
        maxRetries: this.config.retry.maxRetries,
        baseDelayMs: this.config.retry.baseDelayMs,
        maxDelayMs: this.config.retry.maxDelayMs,
        jitterType: this.config.retry.jitterType,
        multiplier: this.config.retry.multiplier,
      } : undefined,
      circuitBreakerOptions: this.config.circuitBreaker?.enabled ? {
        failureThreshold: this.config.circuitBreaker.failureThreshold,
        recoveryTimeout: this.config.circuitBreaker.recoveryTimeout,
        monitoringPeriod: this.config.circuitBreaker.monitoringPeriod,
        expectedErrors: this.config.circuitBreaker.expectedErrors,
      } : undefined,
      rateLimiterOptions: this.config.rateLimiter?.enabled ? {
        tokensPerInterval: this.config.rateLimiter.tokensPerInterval,
        interval: this.config.rateLimiter.interval,
        maxTokens: this.config.rateLimiter.maxTokens,
      } : undefined,
    });
  }

  /**
   * Execute operation with comprehensive resilience patterns
   */
  public async executeResilient<T>(
    operation: () => Promise<T>,
    options?: {
      operationName?: string;
      bulkheadName?: string;
      timeoutMs?: number;
      useAdaptiveTimeout?: boolean;
    }
  ): Promise<T> {
    const operationName = options?.operationName || 'resilient-operation';
    let wrappedOperation = operation;

    // Apply timeout if enabled
    if (this.config.timeout?.enabled && options?.timeoutMs) {
      if (options.useAdaptiveTimeout && this.config.timeout.adaptive?.enabled) {
        const adaptiveTimeout = this.timeoutManager.getAdaptiveTimeout('default', {
          timeoutMs: options.timeoutMs,
          baseTimeoutMs: this.config.timeout.adaptive.baseTimeoutMs,
          maxTimeoutMs: this.config.timeout.adaptive.maxTimeoutMs,
          minTimeoutMs: this.config.timeout.adaptive.minTimeoutMs,
          adaptationFactor: this.config.timeout.adaptive.adaptationFactor,
          windowSize: this.config.timeout.adaptive.windowSize,
        });
        
        wrappedOperation = () => adaptiveTimeout.execute(operation, operationName);
      } else {
        const timeoutWrapper = new TimeoutWrapper({
          timeoutMs: options.timeoutMs,
        });
        
        wrappedOperation = () => timeoutWrapper.execute(operation, operationName);
      }
    }

    // Apply bulkhead if specified
    if (options?.bulkheadName && this.config.bulkhead?.enabled) {
      const bulkhead = this.bulkheadManager.getBulkhead({
        name: options.bulkheadName,
        maxConcurrent: this.config.bulkhead.maxConcurrent,
        maxQueued: this.config.bulkhead.maxQueued,
        timeoutMs: this.config.bulkhead.timeoutMs,
      });
      
      const previousOperation = wrappedOperation;
      wrappedOperation = () => bulkhead.execute(previousOperation, operationName);
    }

    // Apply rate limiting
    if (this.rateLimiter) {
      const previousOperation = wrappedOperation;
      wrappedOperation = async () => {
        await this.rateLimiter!.waitForTokens();
        return previousOperation();
      };
    }

    // Apply circuit breaker
    if (this.circuitBreaker) {
      const previousOperation = wrappedOperation;
      wrappedOperation = () => this.circuitBreaker!.execute(previousOperation, operationName);
    }

    // Apply retry strategy
    if (this.backoffStrategy) {
      const result = await this.backoffStrategy.executeWithRetry(wrappedOperation, operationName);
      if (!result.success) {
        throw result.error;
      }
      return result.result!;
    }

    // Execute without retry if not enabled
    return wrappedOperation();
  }

  /**
   * Get resilient HTTP client
   */
  public getHttpClient(): ResilientHttpClient {
    if (!this.httpClient) {
      throw new Error('HTTP client not initialized');
    }
    return this.httpClient;
  }

  /**
   * Get bulkhead manager
   */
  public getBulkheadManager(): BulkheadManager {
    return this.bulkheadManager;
  }

  /**
   * Get timeout manager
   */
  public getTimeoutManager(): TimeoutManager {
    return this.timeoutManager;
  }

  /**
   * Get comprehensive system health
   */
  public getSystemHealth(): {
    overall: boolean;
    components: {
      circuitBreaker?: CircuitBreakerStats;
      rateLimiter?: { availableTokens: number; maxTokens: number };
      bulkheads: Record<string, BulkheadStats>;
      timeouts: Record<string, TimeoutStats>;
      http?: any;
    };
    bulkheadSystem: ReturnType<BulkheadManager['getSystemHealth']>;
  } {
    const bulkheadSystem = this.bulkheadManager.getSystemHealth();
    
    const components = {
      circuitBreaker: this.circuitBreaker?.getStats(),
      rateLimiter: this.rateLimiter ? {
        availableTokens: this.rateLimiter.getTokenCount(),
        maxTokens: this.config.rateLimiter?.maxTokens || 0,
      } : undefined,
      bulkheads: this.bulkheadManager.getAllStats(),
      timeouts: this.timeoutManager.getAllStats(),
      http: this.httpClient?.getHealthStats(),
    };

    const overall = (
      (!components.circuitBreaker || components.circuitBreaker.state === CircuitState.CLOSED) &&
      (!components.rateLimiter || components.rateLimiter.availableTokens > 0) &&
      bulkheadSystem.healthy
    );

    return {
      overall,
      components,
      bulkheadSystem,
    };
  }

  /**
   * Reset all resilience components
   */
  public reset(): void {
    this.circuitBreaker?.reset();
    this.bulkheadManager.resetAll();
    this.timeoutManager.resetAll();
  }

  /**
   * Update configuration
   */
  public updateConfig(config: Partial<ResilienceConfig>): void {
    this.config = { ...this.config, ...config };
    this.initialize();
  }

  /**
   * Get current configuration
   */
  public getConfig(): ResilienceConfig {
    return { ...this.config };
  }
}

/**
 * Create a pre-configured resilience system for common use cases
 */
export function createResilienceSystem(preset?: 'default' | 'aggressive' | 'conservative' | 'minimal'): ResilienceSystem {
  switch (preset) {
    case 'aggressive':
      return new ResilienceSystem({
        retry: {
          enabled: true,
          maxRetries: 5,
          baseDelayMs: 50,
          maxDelayMs: 10000,
          jitterType: 'full',
          multiplier: 1.5,
        },
        circuitBreaker: {
          enabled: true,
          failureThreshold: 3,
          recoveryTimeout: 30000,
          monitoringPeriod: 60000,
        },
        rateLimiter: {
          enabled: true,
          tokensPerInterval: 200,
          interval: 60000,
          maxTokens: 200,
        },
        bulkhead: {
          enabled: true,
          maxConcurrent: 20,
          maxQueued: 100,
          timeoutMs: 15000,
        },
        timeout: {
          enabled: true,
          timeoutMs: 15000,
          adaptive: {
            enabled: true,
            baseTimeoutMs: 2000,
            maxTimeoutMs: 30000,
            minTimeoutMs: 500,
            adaptationFactor: 0.2,
            windowSize: 50,
          },
        },
      });

    case 'conservative':
      return new ResilienceSystem({
        retry: {
          enabled: true,
          maxRetries: 2,
          baseDelayMs: 200,
          maxDelayMs: 60000,
          jitterType: 'equal',
          multiplier: 3,
        },
        circuitBreaker: {
          enabled: true,
          failureThreshold: 10,
          recoveryTimeout: 120000,
          monitoringPeriod: 300000,
        },
        rateLimiter: {
          enabled: true,
          tokensPerInterval: 50,
          interval: 60000,
          maxTokens: 50,
        },
        bulkhead: {
          enabled: true,
          maxConcurrent: 5,
          maxQueued: 20,
          timeoutMs: 60000,
        },
        timeout: {
          enabled: true,
          timeoutMs: 60000,
          adaptive: {
            enabled: true,
            baseTimeoutMs: 10000,
            maxTimeoutMs: 120000,
            minTimeoutMs: 5000,
            adaptationFactor: 0.05,
            windowSize: 200,
          },
        },
      });

    case 'minimal':
      return new ResilienceSystem({
        retry: {
          enabled: true,
          maxRetries: 1,
          baseDelayMs: 1000,
          maxDelayMs: 5000,
          jitterType: 'none',
          multiplier: 2,
        },
        circuitBreaker: {
          enabled: false,
          failureThreshold: 5,
          recoveryTimeout: 60000,
          monitoringPeriod: 120000,
        },
        rateLimiter: {
          enabled: false,
          tokensPerInterval: 100,
          interval: 60000,
          maxTokens: 100,
        },
        bulkhead: {
          enabled: false,
          maxConcurrent: 10,
          maxQueued: 50,
          timeoutMs: 30000,
        },
        timeout: {
          enabled: true,
          timeoutMs: 30000,
          adaptive: {
            enabled: false,
            baseTimeoutMs: 5000,
            maxTimeoutMs: 60000,
            minTimeoutMs: 1000,
            adaptationFactor: 0.1,
            windowSize: 100,
          },
        },
      });

    case 'default':
    default:
      return new ResilienceSystem(DEFAULT_RESILIENCE_CONFIG);
  }
}