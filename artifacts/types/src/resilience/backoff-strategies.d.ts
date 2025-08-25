/**
 * Exponential Backoff with Full Jitter Implementation
 * Implements resilient retry strategies with various jitter options
 */
export interface RetryOptions {
    maxRetries: number;
    baseDelayMs: number;
    maxDelayMs: number;
    jitterType: 'none' | 'full' | 'equal' | 'decorrelated';
    multiplier: number;
    onRetry?: (attempt: number, delay: number, error: Error) => void;
    shouldRetry?: (error: Error, attempt: number) => boolean;
    timeout?: number;
}
export interface RetryResult<T> {
    success: boolean;
    result?: T;
    error?: Error;
    attempts: number;
    totalTime: number;
    delays: number[];
}
export declare class BackoffStrategy {
    private options;
    constructor(options?: Partial<RetryOptions>);
    /**
     * Execute operation with exponential backoff and full jitter
     */
    executeWithRetry<T>(operation: () => Promise<T>, operationName?: string): Promise<RetryResult<T>>;
    /**
     * Calculate delay with jitter based on strategy
     */
    private calculateDelay;
    /**
     * Execute operation with timeout using AbortController for better resource management
     */
    private executeWithTimeout;
    /**
     * Sleep for specified milliseconds
     */
    private sleep;
    /**
     * Default retry condition - determines if error is retryable
     */
    private isRetryableError;
}
/**
 * Circuit Breaker Pattern Implementation
 */
export declare enum CircuitState {
    CLOSED = "CLOSED",
    OPEN = "OPEN",
    HALF_OPEN = "HALF_OPEN"
}
export interface CircuitBreakerOptions {
    failureThreshold: number;
    recoveryTimeout: number;
    monitoringPeriod: number;
    expectedErrors?: string[];
    onStateChange?: (state: CircuitState, error?: Error) => void;
}
export interface CircuitBreakerStats {
    state: CircuitState;
    failures: number;
    successes: number;
    totalRequests: number;
    lastFailureTime?: number;
    lastSuccessTime?: number;
    uptime: number;
}
export declare class CircuitBreaker {
    private options;
    private state;
    private failures;
    private successes;
    private totalRequests;
    private lastFailureTime?;
    private lastSuccessTime?;
    private nextAttemptTime?;
    private startTime;
    constructor(options: CircuitBreakerOptions);
    /**
     * Execute operation through circuit breaker
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Handle successful operation
     */
    private onSuccess;
    /**
     * Handle failed operation
     */
    private onFailure;
    /**
     * Check if circuit should be opened
     */
    private shouldOpenCircuit;
    /**
     * Check if circuit should attempt reset
     */
    private shouldAttemptReset;
    /**
     * Get time until next attempt is allowed
     */
    private getTimeUntilNextAttempt;
    /**
     * Get circuit breaker statistics
     */
    getStats(): CircuitBreakerStats;
    /**
     * Reset circuit breaker
     */
    reset(): void;
    /**
     * Force circuit open (for testing or maintenance)
     */
    forceOpen(): void;
    /**
     * Force circuit closed
     */
    forceClosed(): void;
    /**
     * Validate circuit breaker options
     */
    private validateOptions;
}
/**
 * Rate Limiter with Token Bucket Algorithm
 */
export interface RateLimiterOptions {
    tokensPerInterval: number;
    interval: number;
    maxTokens: number;
}
export declare class TokenBucketRateLimiter {
    private options;
    private tokens;
    private lastRefillTime;
    constructor(options: RateLimiterOptions);
    /**
     * Try to consume tokens for rate limiting
     */
    consume(tokens?: number): Promise<boolean>;
    /**
     * Wait until tokens are available
     */
    waitForTokens(tokens?: number): Promise<void>;
    /**
     * Get current token count
     */
    getTokenCount(): number;
    /**
     * Get time until next refill
     */
    private getTimeUntilNextRefill;
    /**
     * Refill tokens based on elapsed time
     */
    private refillTokens;
    /**
     * Sleep for specified milliseconds
     */
    private sleep;
    /**
     * Validate rate limiter options
     */
    private validateOptions;
}
/**
 * Resilient HTTP Client with all patterns combined
 */
export interface ResilientHttpOptions {
    retryOptions?: Partial<RetryOptions>;
    circuitBreakerOptions?: CircuitBreakerOptions;
    rateLimiterOptions?: RateLimiterOptions;
    baseURL?: string;
    defaultHeaders?: Record<string, string>;
    timeout?: number;
}
export declare class ResilientHttpClient {
    private options;
    private backoffStrategy;
    private circuitBreaker?;
    private rateLimiter?;
    constructor(options?: ResilientHttpOptions);
    /**
     * Make resilient HTTP request
     */
    request<T>(url: string, options?: RequestInit): Promise<T>;
    /**
     * Execute actual HTTP request
     */
    private executeHttpRequest;
    /**
     * Get system health stats
     */
    getHealthStats(): {
        circuitBreaker: CircuitBreakerStats;
        rateLimiter: {
            availableTokens: number;
            maxTokens: number;
        };
    };
}
