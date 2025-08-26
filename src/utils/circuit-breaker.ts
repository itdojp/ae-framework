import type { EventEmitter } from 'events';
import type { createHash } from 'crypto';

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
  private options: CircuitBreakerOptions;
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
  private halfOpenTimer?: NodeJS.Timeout;

  constructor(
    name: string,
    options: CircuitBreakerOptions
  ) {
    super();
    
    this.name = name;
    this.options = options;
    
    // Validate options
    if (options.failureThreshold <= 0) {
      throw new Error('failureThreshold must be greater than 0');
    }
    if (options.successThreshold <= 0) {
      throw new Error('successThreshold must be greater than 0');
    }
    if (options.timeout <= 0) {
      throw new Error('timeout must be greater than 0');
    }

    this.emit('circuitBreakerCreated', { name: this.name, options: this.options });
  }

  /**
   * Execute a function with circuit breaker protection
   */
  async execute<T>(operation: () => Promise<T>, ...args: any[]): Promise<T> {
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
          return this.options.fallback(...args);
        }
        
        throw new CircuitBreakerOpenError(`Circuit breaker '${this.name}' is OPEN`);
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
      if (this.failureCount >= this.options.failureThreshold) {
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
    this.nextAttempt = Date.now() + this.options.timeout;
    this.circuitOpenCount++;
    this.successCount = 0; // Reset success count

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
    }, this.options.timeout);

    this.emit('stateChange', this.state);
    this.emit('circuitOpened', { 
      name: this.name, 
      previousState,
      failureCount: this.failureCount,
      threshold: this.options.failureThreshold,
      timeout: this.options.timeout
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

    this.emit('stateChange', this.state);
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

    // Clear half-open timer
    if (this.halfOpenTimer) {
      clearTimeout(this.halfOpenTimer);
      this.halfOpenTimer = undefined;
    }

    this.emit('stateChange', this.state);
    this.emit('circuitClosed', { 
      name: this.name, 
      previousState,
      successCount: this.successCount,
      threshold: this.options.successThreshold
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

export default CircuitBreaker;