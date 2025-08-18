import { EventEmitter } from 'events';
import { createHash } from 'crypto';

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
  failureThreshold: number;
  /** Success threshold to close circuit from half-open (default: 3) */
  successThreshold: number;
  /** Timeout before attempting to half-open (ms, default: 60000) */
  timeout: number;
  /** Monitor window for failures (ms, default: 60000) */
  monitoringWindow: number;
  /** Expected error types that should trigger circuit breaking */
  expectedErrors?: Array<new (...args: any[]) => Error>;
  /** Fallback function when circuit is open */
  fallback?: (...args: any[]) => any;
  /** Enable detailed monitoring and metrics */
  enableMonitoring?: boolean;
}

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
 * Request metrics for monitoring
 */
interface RequestMetric {
  timestamp: number;
  duration: number;
  success: boolean;
  error?: Error;
}

/**
 * Circuit Breaker Pattern Implementation for AE-Framework
 * 
 * Provides fault tolerance and resilience for critical operations including:
 * - Agent interactions
 * - External service calls 
 * - Resource-intensive operations
 * - Phase transitions
 * - State management operations
 */
export class CircuitBreaker extends EventEmitter {
  private state: CircuitState = CircuitState.CLOSED;
  private failureCount: number = 0;
  private successCount: number = 0;
  private lastFailureTime: number | null = null;
  private lastSuccessTime: number | null = null;
  private nextAttempt: number = 0;
  private startTime: number = Date.now();

  // Monitoring and metrics
  private requestHistory: RequestMetric[] = [];
  private totalRequests: number = 0;
  private totalFailures: number = 0;
  private totalSuccesses: number = 0;
  private circuitOpenCount: number = 0;
  private responseTimes: number[] = [];

  private readonly options: Required<CircuitBreakerOptions>;
  private readonly name: string;

  constructor(name: string, options: Partial<CircuitBreakerOptions> = {}) {
    super();
    
    this.name = name;
    this.options = {
      failureThreshold: options.failureThreshold ?? 5,
      successThreshold: options.successThreshold ?? 3,
      timeout: options.timeout ?? 60000,
      monitoringWindow: options.monitoringWindow ?? 60000,
      expectedErrors: options.expectedErrors ?? [],
      fallback: options.fallback,
      enableMonitoring: options.enableMonitoring ?? true
    };

    // Clean up old metrics periodically
    if (this.options.enableMonitoring) {
      setInterval(() => this.cleanupMetrics(), this.options.monitoringWindow);
    }

    this.emit('circuitBreakerCreated', { name: this.name, options: this.options });
  }

  /**
   * Execute a function with circuit breaker protection
   */
  async execute<T>(operation: () => Promise<T>, ...args: any[]): Promise<T> {
    const startTime = Date.now();
    this.totalRequests++;

    // Check circuit state
    if (this.state === CircuitState.OPEN) {
      if (Date.now() < this.nextAttempt) {
        this.emit('callRejected', { 
          name: this.name, 
          state: this.state, 
          reason: 'Circuit is open' 
        });
        
        if (this.options.fallback) {
          return this.options.fallback(...args);
        }
        
        throw new CircuitBreakerOpenError(`Circuit breaker '${this.name}' is OPEN`);
      } else {
        // Transition to half-open for testing
        this.state = CircuitState.HALF_OPEN;
        this.emit('stateChanged', { 
          name: this.name, 
          previousState: CircuitState.OPEN, 
          newState: CircuitState.HALF_OPEN 
        });
      }
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
    }
  }

  /**
   * Execute a synchronous function with circuit breaker protection
   */
  executeSync<T>(operation: () => T, ...args: any[]): T {
    const startTime = Date.now();
    this.totalRequests++;

    // Check circuit state
    if (this.state === CircuitState.OPEN) {
      if (Date.now() < this.nextAttempt) {
        this.emit('callRejected', { 
          name: this.name, 
          state: this.state, 
          reason: 'Circuit is open' 
        });
        
        if (this.options.fallback) {
          return this.options.fallback(...args);
        }
        
        throw new CircuitBreakerOpenError(`Circuit breaker '${this.name}' is OPEN`);
      } else {
        // Transition to half-open for testing
        this.state = CircuitState.HALF_OPEN;
        this.emit('stateChanged', { 
          name: this.name, 
          previousState: CircuitState.OPEN, 
          newState: CircuitState.HALF_OPEN 
        });
      }
    }

    try {
      const result = operation();
      const duration = Date.now() - startTime;
      
      this.onSuccess(duration);
      return result;
      
    } catch (error) {
      const duration = Date.now() - startTime;
      this.onFailure(error as Error, duration);
      throw error;
    }
  }

  /**
   * Handle successful operation
   */
  private onSuccess(duration: number): void {
    this.totalSuccesses++;
    this.lastSuccessTime = Date.now();
    this.recordMetric(duration, true);

    if (this.state === CircuitState.HALF_OPEN) {
      this.successCount++;
      
      if (this.successCount >= this.options.successThreshold) {
        this.close();
      }
    } else {
      this.successCount++;
      this.failureCount = 0; // Reset failure count on success
    }

    this.emit('operationSuccess', { 
      name: this.name, 
      duration, 
      state: this.state 
    });
  }

  /**
   * Handle failed operation
   */
  private onFailure(error: Error, duration: number): void {
    this.totalFailures++;
    this.lastFailureTime = Date.now();
    this.recordMetric(duration, false, error);

    // Check if this is an expected error type that should trigger circuit breaking
    const shouldTrip = this.options.expectedErrors.length === 0 || 
                      this.options.expectedErrors.some(ErrorType => error instanceof ErrorType);

    if (shouldTrip) {
      this.failureCount++;
      this.successCount = 0; // Reset success count on failure

      if (this.state === CircuitState.HALF_OPEN) {
        // Failed during testing, go back to open
        this.open();
      } else if (this.failureCount >= this.options.failureThreshold) {
        // Threshold reached, open the circuit
        this.open();
      }
    }

    this.emit('operationFailure', { 
      name: this.name, 
      error, 
      duration, 
      failureCount: this.failureCount,
      state: this.state 
    });
  }

  /**
   * Open the circuit (start failing fast)
   */
  private open(): void {
    const previousState = this.state;
    this.state = CircuitState.OPEN;
    this.nextAttempt = Date.now() + this.options.timeout;
    this.circuitOpenCount++;

    this.emit('stateChanged', { 
      name: this.name, 
      previousState, 
      newState: CircuitState.OPEN,
      nextAttempt: this.nextAttempt
    });

    this.emit('circuitOpened', { 
      name: this.name, 
      failureCount: this.failureCount,
      threshold: this.options.failureThreshold,
      timeout: this.options.timeout
    });
  }

  /**
   * Close the circuit (resume normal operation)
   */
  private close(): void {
    const previousState = this.state;
    this.state = CircuitState.CLOSED;
    this.failureCount = 0;
    this.successCount = 0;

    this.emit('stateChanged', { 
      name: this.name, 
      previousState, 
      newState: CircuitState.CLOSED 
    });

    this.emit('circuitClosed', { 
      name: this.name, 
      successCount: this.successCount,
      threshold: this.options.successThreshold
    });
  }

  /**
   * Force circuit to open (for testing or manual intervention)
   */
  forceOpen(): void {
    this.open();
  }

  /**
   * Force circuit to close (for testing or manual intervention)
   */
  forceClose(): void {
    this.close();
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
   * Get circuit breaker name
   */
  getName(): string {
    return this.name;
  }

  /**
   * Check if circuit is healthy (closed and low failure rate)
   */
  isHealthy(): boolean {
    if (this.state !== CircuitState.CLOSED) {
      return false;
    }

    // Check recent failure rate
    const recentMetrics = this.getRecentMetrics();
    if (recentMetrics.length === 0) {
      return true;
    }

    const failureRate = recentMetrics.filter(m => !m.success).length / recentMetrics.length;
    return failureRate < 0.5; // Healthy if less than 50% failure rate
  }

  /**
   * Record operation metric
   */
  private recordMetric(duration: number, success: boolean, error?: Error): void {
    if (!this.options.enableMonitoring) {
      return;
    }

    const metric: RequestMetric = {
      timestamp: Date.now(),
      duration,
      success,
      error
    };

    this.requestHistory.push(metric);
    this.responseTimes.push(duration);

    // Limit memory usage
    if (this.requestHistory.length > 1000) {
      this.requestHistory = this.requestHistory.slice(-500);
    }
    
    if (this.responseTimes.length > 1000) {
      this.responseTimes = this.responseTimes.slice(-500);
    }
  }

  /**
   * Get recent metrics within monitoring window
   */
  private getRecentMetrics(): RequestMetric[] {
    if (!this.options.enableMonitoring) {
      return [];
    }

    const cutoff = Date.now() - this.options.monitoringWindow;
    return this.requestHistory.filter(metric => metric.timestamp >= cutoff);
  }

  /**
   * Clean up old metrics outside monitoring window
   */
  private cleanupMetrics(): void {
    if (!this.options.enableMonitoring) {
      return;
    }

    const cutoff = Date.now() - this.options.monitoringWindow;
    this.requestHistory = this.requestHistory.filter(metric => metric.timestamp >= cutoff);
  }

  /**
   * Default fallback function
   */
  private defaultFallback(): null {
    return null;
  }

  /**
   * Generate health check report
   */
  generateHealthReport(): {
    name: string;
    state: CircuitState;
    health: 'healthy' | 'degraded' | 'unhealthy';
    stats: CircuitBreakerStats;
    recentFailures: Array<{ timestamp: number; error: string }>;
    recommendations: string[];
  } {
    const stats = this.getStats();
    const recentMetrics = this.getRecentMetrics();
    const recentFailures = recentMetrics
      .filter(m => !m.success && m.error)
      .slice(-5)
      .map(m => ({
        timestamp: m.timestamp,
        error: m.error!.message
      }));

    let health: 'healthy' | 'degraded' | 'unhealthy';
    const recommendations: string[] = [];

    if (this.state === CircuitState.CLOSED && this.isHealthy()) {
      health = 'healthy';
    } else if (this.state === CircuitState.HALF_OPEN || (this.state === CircuitState.CLOSED && !this.isHealthy())) {
      health = 'degraded';
      recommendations.push('Monitor for increasing failure rate');
      if (stats.averageResponseTime > 5000) {
        recommendations.push('Consider reducing timeout or increasing resources');
      }
    } else {
      health = 'unhealthy';
      recommendations.push('Circuit is open - check underlying service health');
      recommendations.push('Consider manual intervention or fallback strategies');
    }

    if (stats.circuitOpenCount > 10) {
      recommendations.push('High number of circuit openings - review failure patterns');
    }

    return {
      name: this.name,
      state: this.state,
      health,
      stats,
      recentFailures,
      recommendations
    };
  }
}

/**
 * Circuit Breaker Open Error
 */
export class CircuitBreakerOpenError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'CircuitBreakerOpenError';
  }
}

/**
 * Circuit Breaker Manager for managing multiple circuit breakers
 */
export class CircuitBreakerManager extends EventEmitter {
  private breakers = new Map<string, CircuitBreaker>();
  private globalStats = {
    totalBreakers: 0,
    openBreakers: 0,
    halfOpenBreakers: 0,
    closedBreakers: 0,
    totalRequests: 0,
    totalFailures: 0
  };

  /**
   * Create or get a circuit breaker by name
   */
  getCircuitBreaker(name: string, options?: Partial<CircuitBreakerOptions>): CircuitBreaker {
    if (!this.breakers.has(name)) {
      const breaker = new CircuitBreaker(name, options);
      
      // Forward events from individual breakers
      breaker.on('stateChanged', (event) => {
        this.updateGlobalStats();
        this.emit('breakerStateChanged', event);
      });
      
      breaker.on('circuitOpened', (event) => {
        this.emit('circuitOpened', event);
      });
      
      breaker.on('circuitClosed', (event) => {
        this.emit('circuitClosed', event);
      });

      this.breakers.set(name, breaker);
      this.globalStats.totalBreakers++;
      this.updateGlobalStats();
    }

    return this.breakers.get(name)!;
  }

  /**
   * Get all circuit breakers
   */
  getAllBreakers(): Map<string, CircuitBreaker> {
    return new Map(this.breakers);
  }

  /**
   * Remove a circuit breaker
   */
  removeCircuitBreaker(name: string): boolean {
    const removed = this.breakers.delete(name);
    if (removed) {
      this.globalStats.totalBreakers--;
      this.updateGlobalStats();
    }
    return removed;
  }

  /**
   * Reset all circuit breakers
   */
  resetAll(): void {
    for (const breaker of this.breakers.values()) {
      breaker.reset();
    }
    this.updateGlobalStats();
  }

  /**
   * Get global statistics across all circuit breakers
   */
  getGlobalStats(): typeof this.globalStats & {
    breakers: Array<{
      name: string;
      state: CircuitState;
      stats: CircuitBreakerStats;
    }>;
  } {
    this.updateGlobalStats();

    const breakers = Array.from(this.breakers.entries()).map(([name, breaker]) => ({
      name,
      state: breaker.getState(),
      stats: breaker.getStats()
    }));

    return {
      ...this.globalStats,
      breakers
    };
  }

  /**
   * Generate comprehensive health report for all circuit breakers
   */
  generateHealthReport(): {
    overall: 'healthy' | 'degraded' | 'unhealthy';
    summary: typeof this.globalStats;
    breakers: ReturnType<CircuitBreaker['generateHealthReport']>[];
  } {
    const breakerReports = Array.from(this.breakers.values()).map(breaker => 
      breaker.generateHealthReport()
    );

    const unhealthyCount = breakerReports.filter(r => r.health === 'unhealthy').length;
    const degradedCount = breakerReports.filter(r => r.health === 'degraded').length;

    let overall: 'healthy' | 'degraded' | 'unhealthy';
    if (unhealthyCount > 0) {
      overall = 'unhealthy';
    } else if (degradedCount > 0) {
      overall = 'degraded';
    } else {
      overall = 'healthy';
    }

    return {
      overall,
      summary: this.globalStats,
      breakers: breakerReports
    };
  }

  /**
   * Update global statistics
   */
  private updateGlobalStats(): void {
    let openBreakers = 0;
    let halfOpenBreakers = 0;
    let closedBreakers = 0;
    let totalRequests = 0;
    let totalFailures = 0;

    for (const breaker of this.breakers.values()) {
      const state = breaker.getState();
      const stats = breaker.getStats();

      switch (state) {
        case CircuitState.OPEN:
          openBreakers++;
          break;
        case CircuitState.HALF_OPEN:
          halfOpenBreakers++;
          break;
        case CircuitState.CLOSED:
          closedBreakers++;
          break;
      }

      totalRequests += stats.totalRequests;
      totalFailures += stats.totalFailures;
    }

    this.globalStats.openBreakers = openBreakers;
    this.globalStats.halfOpenBreakers = halfOpenBreakers;
    this.globalStats.closedBreakers = closedBreakers;
    this.globalStats.totalRequests = totalRequests;
    this.globalStats.totalFailures = totalFailures;
  }
}

// Global circuit breaker manager instance
export const circuitBreakerManager = new CircuitBreakerManager();