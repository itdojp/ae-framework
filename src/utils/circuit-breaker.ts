import { EventEmitter } from 'events';
import type { createHash } from 'crypto';

export type ErrorConstructorLike =
  | (new (message: string, ...rest: unknown[]) => Error)
  | (new (...args: [] | [message: string, ...rest: unknown[]]) => Error);
export type FallbackHandler<TResult = unknown> = (...args: unknown[]) => TResult;

/**
 * Circuit Breaker States
 */
export enum CircuitState {
  CLOSED = 'CLOSED',     // Normal operation
  OPEN = 'OPEN',         // Failing fast, rejecting calls
  HALF_OPEN = 'HALF_OPEN' // Testing if service has recovered
}

/**
 * Circuit Breaker Configuration Options
 */
export interface CircuitBreakerOptions {
  /** Failure threshold to open circuit (default: 5) */
  failureThreshold?: number;
  /** Success threshold to close circuit from half-open (default: 3) */
  successThreshold?: number;
  /** Timeout before attempting to half-open (ms, default: 60000) */
  timeout?: number;
  /** Monitor window for failures (ms, default: 60000) */
  monitoringWindow?: number;
  /** Expected error types that should trigger circuit breaking */
  expectedErrors?: ReadonlyArray<ErrorConstructorLike>;
  /** Fallback function when circuit is open */
  fallback?: FallbackHandler;
  /** Enable detailed monitoring and metrics */
  enableMonitoring?: boolean;
  /** Maximum concurrent calls allowed while HALF_OPEN (default: Infinity) */
  halfOpenMaxCalls?: number;
  /** Alias for timeout when transitioning from OPEN to HALF_OPEN */
  resetTimeoutMs?: number;
}

type NormalizedCircuitBreakerOptions = {
  failureThreshold: number;
  successThreshold: number;
  timeout: number;
  resetTimeoutMs: number;
  monitoringWindow: number;
  expectedErrors: ReadonlyArray<ErrorConstructorLike>;
  fallback?: FallbackHandler;
  enableMonitoring: boolean;
  halfOpenMaxCalls: number;
};

/**
 * Circuit Breaker Statistics
 */
export interface CircuitBreakerStats {
  state: CircuitState;
  failureCount: number;
  successCount: number;
  lastFailureTime: number | null;
  lastSuccessTime: number | null;
  totalRequests: number;
  totalFailures: number;
  totalSuccesses: number;
  circuitOpenCount: number;
  averageResponseTime: number;
  uptime: number;
}

/**
 * Circuit Breaker Error
 */
export class CircuitBreakerOpenError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'CircuitBreakerOpenError';
  }
}

/**
 * Circuit Breaker Implementation with Auto-Recovery
 */
export class CircuitBreaker extends EventEmitter {
  private name: string;
  private options: NormalizedCircuitBreakerOptions;
  private state: CircuitState = CircuitState.CLOSED;
  private failureCount: number = 0;
  private successCount: number = 0;
  private lastFailureTime: number | null = null;
  private lastSuccessTime: number | null = null;
  private nextAttempt: number = 0;
  private totalRequests: number = 0;
  private totalFailures: number = 0;
  private totalSuccesses: number = 0;
  private circuitOpenCount: number = 0;
  private readonly startTime: number = Date.now();
  private responseTimes: number[] = [];
  private requestHistory: Array<{ timestamp: number; success: boolean }> = [];
  private halfOpenTimer: NodeJS.Timeout | undefined;
  private halfOpenActiveCalls: number = 0;
  private halfOpenAttemptCount: number = 0;

  constructor(
    name: string,
    options: CircuitBreakerOptions
  ) {
    super();

    this.name = name;
    const defaultTimeout = options.timeout ?? options.resetTimeoutMs ?? 60000;
    const normalized: NormalizedCircuitBreakerOptions = {
      failureThreshold: options.failureThreshold ?? 5,
      successThreshold: options.successThreshold ?? 3,
      timeout: defaultTimeout,
      resetTimeoutMs: options.resetTimeoutMs ?? defaultTimeout,
      monitoringWindow: options.monitoringWindow ?? 60000,
      expectedErrors: options.expectedErrors ?? [],
      enableMonitoring: options.enableMonitoring ?? false,
      halfOpenMaxCalls: options.halfOpenMaxCalls ?? Number.POSITIVE_INFINITY,
    };

    if (options.fallback) {
      normalized.fallback = options.fallback;
    }

    this.options = normalized;

    // Validate options
    if ((this.options.failureThreshold ?? 0) <= 0) {
      throw new Error('failureThreshold must be greater than 0');
    }
    if ((this.options.successThreshold ?? 0) <= 0) {
      throw new Error('successThreshold must be greater than 0');
    }
    if ((this.options.timeout ?? 0) <= 0) {
      throw new Error('timeout must be greater than 0');
    }

    this.emit('circuitBreakerCreated', { name: this.name, options: this.options });
  }


  /**
   * Execute a function with circuit breaker protection
   */
  async execute<T>(operation: () => Promise<T>, ...args: unknown[]): Promise<T> {
    const startTime = Date.now();
    this.totalRequests++;

    // Check circuit state and handle transitions
    if (this.state === CircuitState.OPEN) {
      if (Date.now() >= this.nextAttempt) {
        // Time to attempt half-open
        this.transitionToHalfOpen();
      } else {
        // Still in OPEN state, reject call
        this.emit('callRejected', { 
          name: this.name, 
          state: this.state, 
          reason: 'Circuit is open' 
        });
        
        if (this.options.fallback) {
          return this.options.fallback(...args) as T;
        }
        
        throw new CircuitBreakerOpenError(`Circuit breaker '${this.name}' is OPEN`);
      }
    }

    const isHalfOpenCall = this.state === CircuitState.HALF_OPEN;
    if (isHalfOpenCall) {
      const maxCalls = this.options.halfOpenMaxCalls ?? Number.POSITIVE_INFINITY;
      if (Number.isFinite(maxCalls) && this.halfOpenAttemptCount >= maxCalls) {
        this.emit('callRejected', {
          name: this.name,
          state: this.state,
          reason: 'Half-open max calls exceeded',
        });
        this.transitionToOpen();
        if (this.options.fallback) {
          return this.options.fallback(...args) as T;
        }
        throw new CircuitBreakerOpenError(`Circuit breaker '${this.name}' is HALF_OPEN`);
      }
      this.halfOpenActiveCalls++;
      this.halfOpenAttemptCount++;
    }

    try {
      const result = await operation();
      const duration = Date.now() - startTime;
      
      this.onSuccess(duration);
      return result;
      
    } catch (error) {
      const duration = Date.now() - startTime;
      this.onFailure(error as Error, duration);
      throw error;
    } finally {
      if (isHalfOpenCall) {
        this.halfOpenActiveCalls = Math.max(0, this.halfOpenActiveCalls - 1);
      }
    }
  }

  /**
   * Handle successful operation
   */
  private onSuccess(duration: number): void {
    this.successCount++;
    this.totalSuccesses++;
    this.lastSuccessTime = Date.now();
    
    if (this.options.enableMonitoring) {
      this.responseTimes.push(duration);
      this.requestHistory.push({ timestamp: Date.now(), success: true });
      this.cleanupOldHistory();
    }

    // State transition logic for HALF_OPEN → CLOSED
    if (this.state === CircuitState.HALF_OPEN) {
      if (this.successCount >= this.options.successThreshold) {
        this.transitionToClosed();
      }
    } else if (this.state === CircuitState.CLOSED) {
      // Reset failure count on success in CLOSED state
      this.failureCount = 0;
    }

    this.emit('operationSuccess', { 
      name: this.name, 
      duration, 
      state: this.state,
      successCount: this.successCount 
    });
  }

  /**
   * Handle failed operation
   */
  private onFailure(error: Error, duration: number): void {
    // Respect expectedErrors: only count specified error types toward failure threshold
    if (this.options.expectedErrors && this.options.expectedErrors.length > 0) {
      const isExpected = this.options.expectedErrors.some((Err) => error instanceof Err);
      if (!isExpected) {
        // Not an expected error – treat as non-fatal for breaker state (no state change)
        if (this.options.enableMonitoring) {
          this.responseTimes.push(duration);
          this.requestHistory.push({ timestamp: Date.now(), success: false });
          this.cleanupOldHistory();
        }
        this.emit('operationFailure', {
          name: this.name,
          error: error.message,
          duration,
          state: this.state,
          failureCount: this.failureCount,
        });
        return;
      }
    }

    this.failureCount++;
    this.totalFailures++;
    this.lastFailureTime = Date.now();
    
    if (this.options.enableMonitoring) {
      this.responseTimes.push(duration);
      this.requestHistory.push({ timestamp: Date.now(), success: false });
      this.cleanupOldHistory();
    }

    // State transition logic
    if (this.state === CircuitState.HALF_OPEN) {
      // Any failure in HALF_OPEN goes back to OPEN
      this.transitionToOpen();
    } else if (this.state === CircuitState.CLOSED) {
      // Check if we should open the circuit
      if (this.failureCount >= (this.options.failureThreshold ?? 0)) {
        this.transitionToOpen();
      }
    }

    this.emit('operationFailure', { 
      name: this.name, 
      error: error.message, 
      duration, 
      state: this.state,
      failureCount: this.failureCount 
    });
  }

  /**
   * Transition to OPEN state
   */
  private transitionToOpen(): void {
    const previousState = this.state;
    this.state = CircuitState.OPEN;
    const resetDelay = this.options.resetTimeoutMs ?? this.options.timeout ?? 60000;
    this.nextAttempt = Date.now() + resetDelay;
    this.circuitOpenCount++;
    this.successCount = 0; // Reset success count
    this.halfOpenActiveCalls = 0;
    this.halfOpenAttemptCount = 0;
    this.halfOpenAttemptCount = 0;
    this.halfOpenAttemptCount = 0;
    this.halfOpenAttemptCount = 0;

    // Clear any existing half-open timer
    if (this.halfOpenTimer) {
      clearTimeout(this.halfOpenTimer);
      this.halfOpenTimer = undefined;
    }

    // Schedule automatic transition to HALF_OPEN
    this.halfOpenTimer = setTimeout(() => {
      if (this.state === CircuitState.OPEN) {
        this.transitionToHalfOpen();
      }
    }, resetDelay);

    this.emit('stateChange', { name: this.name, state: this.state });
    this.emit('stateChanged', { name: this.name, previousState, newState: this.state });
    this.emit('circuitOpened', {
      name: this.name,
      failureCount: this.failureCount,
      threshold: this.options.failureThreshold,
      timeout: this.options.timeout,
    });
  }

  /**
   * Transition to HALF_OPEN state
   */
  private transitionToHalfOpen(): void {
    const previousState = this.state;
    this.state = CircuitState.HALF_OPEN;
    this.successCount = 0;
    this.failureCount = 0;
    this.halfOpenActiveCalls = 0;

    this.emit('stateChange', { name: this.name, state: this.state });
    this.emit('stateChanged', { name: this.name, previousState, newState: this.state });
    this.emit('circuitHalfOpen', { 
      name: this.name, 
      previousState 
    });
  }

  /**
   * Transition to CLOSED state
   */
  private transitionToClosed(): void {
    const previousState = this.state;
    this.state = CircuitState.CLOSED;
    this.failureCount = 0;
    this.successCount = 0;
    this.halfOpenActiveCalls = 0;

    // Clear half-open timer
    if (this.halfOpenTimer) {
      clearTimeout(this.halfOpenTimer);
      this.halfOpenTimer = undefined;
    }

    this.emit('stateChange', { name: this.name, state: this.state });
    this.emit('stateChanged', { name: this.name, previousState, newState: this.state });
    this.emit('circuitClosed', {
      name: this.name,
      successCount: this.successCount,
      threshold: this.options.successThreshold,
    });
  }

  /**
   * Clean up old request history
   */
  private cleanupOldHistory(): void {
    if (!this.options.enableMonitoring) return;
    
    const cutoff = Date.now() - this.options.monitoringWindow;
    this.requestHistory = this.requestHistory.filter(req => req.timestamp > cutoff);
    
    // Keep only recent response times (last 100)
    if (this.responseTimes.length > 100) {
      this.responseTimes = this.responseTimes.slice(-100);
    }
  }

  /**
   * Get current circuit breaker statistics
   */
  getStats(): CircuitBreakerStats {
    const now = Date.now();
    const averageResponseTime = this.responseTimes.length > 0 
      ? this.responseTimes.reduce((sum, time) => sum + time, 0) / this.responseTimes.length 
      : 0;

    return {
      state: this.state,
      failureCount: this.failureCount,
      successCount: this.successCount,
      lastFailureTime: this.lastFailureTime,
      lastSuccessTime: this.lastSuccessTime,
      totalRequests: this.totalRequests,
      totalFailures: this.totalFailures,
      totalSuccesses: this.totalSuccesses,
      circuitOpenCount: this.circuitOpenCount,
      averageResponseTime,
      uptime: now - this.startTime
    };
  }

  /**
   * Get current circuit state
   */
  getState(): CircuitState {
    return this.state;
  }

  /**
   * Get circuit name
   */
  getName(): string {
    return this.name;
  }

  /**
   * Force circuit to open (for testing or manual intervention)
   */
  forceOpen(): void {
    this.transitionToOpen();
  }

  /**
   * Force circuit to close (for testing or manual intervention)
   */
  forceClose(): void {
    this.transitionToClosed();
  }

  /**
   * Reset circuit breaker to initial state
   */
  reset(): void {
    const previousState = this.state;
    this.state = CircuitState.CLOSED;
    this.failureCount = 0;
    this.successCount = 0;
    this.lastFailureTime = null;
    this.lastSuccessTime = null;
    this.nextAttempt = 0;
    this.halfOpenActiveCalls = 0;

    // Clear timer
    if (this.halfOpenTimer) {
      clearTimeout(this.halfOpenTimer);
      this.halfOpenTimer = undefined;
    }

    // Reset total counters
    this.totalRequests = 0;
    this.totalFailures = 0;
    this.totalSuccesses = 0;
    this.circuitOpenCount = 0;

    if (this.options.enableMonitoring) {
      this.requestHistory = [];
      this.responseTimes = [];
    }

    this.emit('circuitReset', { 
      name: this.name, 
      previousState 
    });
  }

  /**
   * Generate health report for monitoring
   */
  generateHealthReport(): {
    name: string;
    state: CircuitState;
    health: 'healthy' | 'degraded' | 'unhealthy';
    recommendations: string[];
    stats: CircuitBreakerStats;
    recentFailures: number[];
  } {
    const stats = this.getStats();
    const recommendations: string[] = [];
    let health: 'healthy' | 'degraded' | 'unhealthy' = 'healthy';

    if (this.state === CircuitState.OPEN) {
      health = 'unhealthy';
      recommendations.push('Circuit is open - check underlying service health');
    } else if (this.state === CircuitState.HALF_OPEN) {
      health = 'degraded';
      recommendations.push('Circuit is recovering - monitor closely');
    } else {
      const failureRate = stats.totalRequests > 0 ? stats.totalFailures / stats.totalRequests : 0;
      if (failureRate > 0.3) {
        health = 'degraded';
        recommendations.push(`High failure rate: ${(failureRate * 100).toFixed(1)}%`);
      }
      if (stats.averageResponseTime > this.options.timeout * 0.8) {
        health = 'degraded';
        recommendations.push(`Slow response times: ${stats.averageResponseTime.toFixed(0)}ms avg`);
      }
    }

    const recentFailures = this.requestHistory
      .filter((r) => !r.success)
      .map((r) => r.timestamp);
    return {
      name: this.name,
      state: this.state,
      health,
      recommendations,
      stats,
      recentFailures,
    };
  }

  /**
   * Execute a synchronous function with circuit breaker protection
   */
  executeSync<T>(operation: () => T, ...args: unknown[]): T {
    const startTime = Date.now();
    this.totalRequests++;

    if (this.state === CircuitState.OPEN) {
      if (Date.now() >= this.nextAttempt) {
        this.transitionToHalfOpen();
      } else {
        this.emit('callRejected', { name: this.name, state: this.state, reason: 'Circuit is open' });
        if (this.options.fallback) {
          return this.options.fallback(...args) as T;
        }
        throw new CircuitBreakerOpenError(`Circuit breaker '${this.name}' is OPEN`);
      }
    }

    try {
      const result = operation();
      const duration = Date.now() - startTime;
      this.onSuccess(duration);
      return result;
    } catch (err) {
      const duration = Date.now() - startTime;
      this.onFailure(err as Error, duration);
      throw err;
    }
  }

  /**
   * Check if circuit breaker is in a healthy state
   */
  isHealthy(): boolean {
    // Circuit is healthy if it's closed or half-open with recent successes
    if (this.state === CircuitState.CLOSED) {
      // Check recent failure rate in closed state
      const recentFailureRate = this.totalRequests > 0 ? this.failureCount / this.totalRequests : 0;
      return recentFailureRate < 0.5; // Healthy if failure rate < 50%
    }
    
    if (this.state === CircuitState.HALF_OPEN) {
      // Healthy if we have some recent successes
      return this.successCount > 0;
    }
    
    // Open state is not healthy
    return false;
  }

  /**
   * Cleanup resources
   */
  destroy(): void {
    if (this.halfOpenTimer) {
      clearTimeout(this.halfOpenTimer);
      this.halfOpenTimer = undefined;
    }
    this.removeAllListeners();
  }
}

/**
 * Simple Circuit Breaker Manager
 */
export class CircuitBreakerManager extends EventEmitter {
  private breakers = new Map<string, CircuitBreaker>();

  private static readonly DEFAULT_OPTIONS: CircuitBreakerOptions = {
    failureThreshold: 5,
    successThreshold: 3,
    timeout: 60_000,
    monitoringWindow: 60_000,
    enableMonitoring: false,
  };

  getCircuitBreaker(name: string, options?: Partial<CircuitBreakerOptions>): CircuitBreaker {
    if (!this.breakers.has(name)) {
      const merged: CircuitBreakerOptions = {
        ...CircuitBreakerManager.DEFAULT_OPTIONS,
        ...(options || {}),
      } as CircuitBreakerOptions;
      const breaker = new CircuitBreaker(name, merged);
      this.breakers.set(name, breaker);

      // Forward events
      breaker.on('stateChange', (state) => this.emit('breakerStateChanged', { name, state }));
      breaker.on('circuitOpened', (event) => this.emit('circuitOpened', event));
      breaker.on('circuitClosed', (event) => this.emit('circuitClosed', event));
    }

    const breaker = this.breakers.get(name);
    if (!breaker) {
      throw new Error(`CircuitBreaker for "${name}" was not found after creation.`);
    }
    return breaker;
  }

  getAllBreakers(): Map<string, CircuitBreaker> {
    return this.breakers;
  }

  removeCircuitBreaker(name: string): boolean {
    const breaker = this.breakers.get(name);
    if (!breaker) return false;
    breaker.destroy();
    return this.breakers.delete(name);
  }

  resetAll(): void {
    for (const breaker of this.breakers.values()) {
      breaker.reset();
    }
  }

  getGlobalStats(): {
    totalBreakers: number;
    openBreakers: number;
    closedBreakers: number;
    halfOpenBreakers: number;
    totalRequests: number;
    totalFailures: number;
    breakers: Array<{ name: string; state: CircuitState; stats: CircuitBreakerStats }>;
  } {
    const breakers = Array.from(this.breakers.entries());
    let open = 0, closed = 0, half = 0, totalReq = 0, totalFail = 0;
    const details = breakers.map(([name, b]) => {
      const s = b.getStats();
      switch (b.getState()) {
        case CircuitState.OPEN: open++; break;
        case CircuitState.HALF_OPEN: half++; break;
        case CircuitState.CLOSED: default: closed++; break;
      }
      totalReq += s.totalRequests;
      totalFail += s.totalFailures;
      return { name, state: b.getState(), stats: s };
    });
    return {
      totalBreakers: breakers.length,
      openBreakers: open,
      closedBreakers: closed,
      halfOpenBreakers: half,
      totalRequests: totalReq,
      totalFailures: totalFail,
      breakers: details,
    };
  }

  generateHealthReport(): {
    overall: 'healthy' | 'degraded' | 'unhealthy';
    summary: {
      totalBreakers: number;
      openBreakers: number;
      closedBreakers: number;
      halfOpenBreakers: number;
    };
    breakers: Array<{ name: string; health: 'healthy' | 'degraded' | 'unhealthy'; recommendations: string[] }>;
  } {
    const stats = this.getGlobalStats();
    const breakers = Array.from(this.breakers.entries()).map(([name, b]) => {
      const { health, recommendations } = b.generateHealthReport();
      return { name, health, recommendations };
    });
    const overall = stats.openBreakers > 0 ? 'unhealthy' : (stats.halfOpenBreakers > 0 ? 'degraded' : 'healthy');
    return {
      overall,
      summary: {
        totalBreakers: stats.totalBreakers,
        openBreakers: stats.openBreakers,
        closedBreakers: stats.closedBreakers,
        halfOpenBreakers: stats.halfOpenBreakers,
      },
      breakers,
    };
  }
}

export const circuitBreakerManager = new CircuitBreakerManager();
export default CircuitBreaker;
