import { EventEmitter } from 'events';
/**
 * Circuit Breaker States
 */
export declare enum CircuitState {
    CLOSED = "CLOSED",// Normal operation
    OPEN = "OPEN",// Failing fast, rejecting calls
    HALF_OPEN = "HALF_OPEN"
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
export declare class CircuitBreakerOpenError extends Error {
    constructor(message: string);
}
/**
 * Circuit Breaker Implementation with Auto-Recovery
 */
export declare class CircuitBreaker extends EventEmitter {
    private name;
    private options;
    private state;
    private failureCount;
    private successCount;
    private lastFailureTime;
    private lastSuccessTime;
    private nextAttempt;
    private totalRequests;
    private totalFailures;
    private totalSuccesses;
    private circuitOpenCount;
    private readonly startTime;
    private responseTimes;
    private requestHistory;
    private halfOpenTimer?;
    constructor(name: string, options: CircuitBreakerOptions);
    /**
     * Execute a function with circuit breaker protection
     */
    execute<T>(operation: () => Promise<T>, ...args: any[]): Promise<T>;
    /**
     * Handle successful operation
     */
    private onSuccess;
    /**
     * Handle failed operation
     */
    private onFailure;
    /**
     * Transition to OPEN state
     */
    private transitionToOpen;
    /**
     * Transition to HALF_OPEN state
     */
    private transitionToHalfOpen;
    /**
     * Transition to CLOSED state
     */
    private transitionToClosed;
    /**
     * Clean up old request history
     */
    private cleanupOldHistory;
    /**
     * Get current circuit breaker statistics
     */
    getStats(): CircuitBreakerStats;
    /**
     * Get current circuit state
     */
    getState(): CircuitState;
    /**
     * Get circuit name
     */
    getName(): string;
    /**
     * Force circuit to open (for testing or manual intervention)
     */
    forceOpen(): void;
    /**
     * Force circuit to close (for testing or manual intervention)
     */
    forceClose(): void;
    /**
     * Reset circuit breaker to initial state
     */
    reset(): void;
    /**
     * Check if circuit breaker is in a healthy state
     */
    isHealthy(): boolean;
    /**
     * Cleanup resources
     */
    destroy(): void;
}
export default CircuitBreaker;
