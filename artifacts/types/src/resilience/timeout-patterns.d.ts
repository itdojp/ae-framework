/**
 * Advanced Timeout Patterns Implementation
 * Provides sophisticated timeout handling strategies
 */
export interface TimeoutOptions {
    timeoutMs: number;
    onTimeout?: (duration: number) => void;
    abortController?: AbortController;
    timeoutMessage?: string;
}
export interface AdaptiveTimeoutOptions extends TimeoutOptions {
    baseTimeoutMs: number;
    maxTimeoutMs: number;
    minTimeoutMs: number;
    adaptationFactor: number;
    windowSize: number;
}
export interface TimeoutStats {
    totalOperations: number;
    timeouts: number;
    successfulOperations: number;
    averageExecutionTime: number;
    timeoutRate: number;
    currentTimeoutMs: number;
}
/**
 * Basic timeout wrapper for operations
 */
export declare class TimeoutWrapper {
    private options;
    constructor(options: TimeoutOptions);
    /**
     * Execute operation with timeout
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    private validateOptions;
}
/**
 * Custom timeout error
 */
export declare class TimeoutError extends Error {
    readonly timeoutMs: number;
    readonly actualDuration: number;
    readonly name = "TimeoutError";
    constructor(message: string, timeoutMs: number, actualDuration: number);
}
/**
 * Adaptive timeout that adjusts based on historical performance
 */
export declare class AdaptiveTimeout {
    private options;
    private executionTimes;
    private totalOperations;
    private timeouts;
    private successfulOperations;
    private currentTimeoutMs;
    constructor(options: AdaptiveTimeoutOptions);
    /**
     * Execute operation with adaptive timeout
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Record successful operation and adapt timeout
     */
    private recordSuccess;
    /**
     * Adapt timeout based on recent performance
     */
    private adaptTimeout;
    /**
     * Calculate percentile from sorted array
     */
    private calculatePercentile;
    /**
     * Get timeout statistics
     */
    getStats(): TimeoutStats;
    /**
     * Reset statistics and timeout to base value
     */
    reset(): void;
    /**
     * Get current timeout value
     */
    getCurrentTimeout(): number;
    /**
     * Manually set timeout value
     */
    setTimeout(timeoutMs: number): void;
    private validateOptions;
}
/**
 * Hierarchical timeout with cascading timeouts for nested operations
 */
export declare class HierarchicalTimeout {
    private static readonly MAX_TIMEOUT_MS;
    private static readonly FALLBACK_TIMEOUT_MS;
    private activeTimeouts;
    private operationStack;
    /**
     * Execute operation with hierarchical timeout
     */
    executeWithHierarchy<T>(operation: () => Promise<T>, operationId: string, timeoutMs: number, parentOperationId?: string): Promise<T>;
    /**
     * Clean up operation timeout
     */
    private cleanupOperation;
    /**
     * Cancel all active timeouts
     */
    cancelAll(): void;
    /**
     * Get active operations
     */
    getActiveOperations(): string[];
    /**
     * Check if operation is active
     */
    isOperationActive(operationId: string): boolean;
}
/**
 * Timeout manager for coordinating multiple timeout strategies
 */
export declare class TimeoutManager {
    private adaptiveTimeouts;
    private hierarchicalTimeout;
    /**
     * Create or get adaptive timeout instance
     */
    getAdaptiveTimeout(name: string, options: AdaptiveTimeoutOptions): AdaptiveTimeout;
    /**
     * Execute with adaptive timeout
     */
    executeWithAdaptiveTimeout<T>(name: string, operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Execute with hierarchical timeout
     */
    executeWithHierarchicalTimeout<T>(operation: () => Promise<T>, operationId: string, timeoutMs: number, parentOperationId?: string): Promise<T>;
    /**
     * Get all timeout statistics
     */
    getAllStats(): Record<string, TimeoutStats>;
    /**
     * Reset all timeout managers
     */
    resetAll(): void;
    /**
     * Get active hierarchical operations
     */
    getActiveHierarchicalOperations(): string[];
    /**
     * Cancel all active operations
     */
    cancelAllOperations(): void;
}
