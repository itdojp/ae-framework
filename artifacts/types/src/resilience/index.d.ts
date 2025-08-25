/**
 * Comprehensive Resilience System
 * Exports all resilience patterns and utilities
 */
import { ResilientHttpClient, type CircuitBreakerStats } from './backoff-strategies.js';
import { BulkheadManager, type BulkheadStats } from './bulkhead-isolation.js';
import { TimeoutManager, type TimeoutStats } from './timeout-patterns.js';
export { BackoffStrategy, CircuitBreaker, CircuitState, TokenBucketRateLimiter, ResilientHttpClient, type RetryOptions, type RetryResult, type CircuitBreakerOptions, type CircuitBreakerStats, type RateLimiterOptions, type ResilientHttpOptions, } from './backoff-strategies.js';
export { Bulkhead, BulkheadManager, type BulkheadOptions, type BulkheadStats, } from './bulkhead-isolation.js';
export { TimeoutWrapper, AdaptiveTimeout, HierarchicalTimeout, TimeoutManager, TimeoutError, type TimeoutOptions, type AdaptiveTimeoutOptions, type TimeoutStats, } from './timeout-patterns.js';
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
export declare const DEFAULT_RESILIENCE_CONFIG: ResilienceConfig;
/**
 * Comprehensive resilience system that combines all patterns
 */
export declare class ResilienceSystem {
    private config;
    private backoffStrategy?;
    private circuitBreaker?;
    private rateLimiter?;
    private bulkheadManager;
    private timeoutManager;
    private httpClient?;
    constructor(config?: ResilienceConfig);
    /**
     * Initialize resilience components based on configuration
     */
    private initialize;
    /**
     * Execute operation with comprehensive resilience patterns
     */
    executeResilient<T>(operation: () => Promise<T>, options?: {
        operationName?: string;
        bulkheadName?: string;
        timeoutMs?: number;
        useAdaptiveTimeout?: boolean;
    }): Promise<T>;
    /**
     * Get resilient HTTP client
     */
    getHttpClient(): ResilientHttpClient;
    /**
     * Get bulkhead manager
     */
    getBulkheadManager(): BulkheadManager;
    /**
     * Get timeout manager
     */
    getTimeoutManager(): TimeoutManager;
    /**
     * Get comprehensive system health
     */
    getSystemHealth(): {
        overall: boolean;
        components: {
            circuitBreaker?: CircuitBreakerStats;
            rateLimiter?: {
                availableTokens: number;
                maxTokens: number;
            };
            bulkheads: Record<string, BulkheadStats>;
            timeouts: Record<string, TimeoutStats>;
            http?: any;
        };
        bulkheadSystem: ReturnType<BulkheadManager['getSystemHealth']>;
    };
    /**
     * Reset all resilience components
     */
    reset(): void;
    /**
     * Update configuration
     */
    updateConfig(config: Partial<ResilienceConfig>): void;
    /**
     * Get current configuration
     */
    getConfig(): ResilienceConfig;
}
/**
 * Create a pre-configured resilience system for common use cases
 */
export declare function createResilienceSystem(preset?: 'default' | 'aggressive' | 'conservative' | 'minimal'): ResilienceSystem;
