/**
 * Bulkhead Isolation Pattern Implementation
 * Isolates critical resources to prevent cascading failures
 */
export interface BulkheadOptions {
    name: string;
    maxConcurrent: number;
    maxQueued: number;
    timeoutMs: number;
    onReject?: (reason: 'capacity' | 'timeout' | 'queue_full') => void;
}
export interface BulkheadStats {
    name: string;
    active: number;
    queued: number;
    maxConcurrent: number;
    maxQueued: number;
    totalExecuted: number;
    totalRejected: number;
    averageExecutionTime: number;
    rejectionReasons: Record<string, number>;
}
export declare class Bulkhead {
    private options;
    private active;
    private queue;
    private totalExecuted;
    private totalRejected;
    private executionTimes;
    private rejectionReasons;
    constructor(options: BulkheadOptions);
    /**
     * Execute operation within bulkhead constraints
     */
    execute<T>(operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Execute operation immediately
     */
    private executeImmediately;
    /**
     * Process queued operations
     */
    private processQueue;
    /**
     * Remove operation from queue
     */
    private removeFromQueue;
    /**
     * Handle operation rejection
     */
    private handleRejection;
    /**
     * Record successful execution
     */
    private recordExecution;
    /**
     * Get bulkhead statistics
     */
    getStats(): BulkheadStats;
    /**
     * Reset bulkhead statistics
     */
    reset(): void;
    /**
     * Get current load factor (0-1)
     */
    getLoadFactor(): number;
    /**
     * Check if bulkhead is healthy
     */
    isHealthy(): boolean;
    /**
     * Validate bulkhead options
     */
    private validateOptions;
}
/**
 * Bulkhead Manager for managing multiple isolated bulkheads
 */
export declare class BulkheadManager {
    private bulkheads;
    /**
     * Create or get a bulkhead
     */
    getBulkhead(options: BulkheadOptions): Bulkhead;
    /**
     * Execute operation in named bulkhead
     */
    executeInBulkhead<T>(bulkheadName: string, operation: () => Promise<T>, operationName?: string): Promise<T>;
    /**
     * Get all bulkhead statistics
     */
    getAllStats(): Record<string, BulkheadStats>;
    /**
     * Get system health across all bulkheads
     */
    getSystemHealth(): {
        healthy: boolean;
        totalBulkheads: number;
        healthyBulkheads: number;
        totalActive: number;
        totalQueued: number;
        averageLoadFactor: number;
    };
    /**
     * Reset all bulkheads
     */
    resetAll(): void;
    /**
     * Remove a bulkhead
     */
    removeBulkhead(name: string): boolean;
    /**
     * Get bulkhead names
     */
    getBulkheadNames(): string[];
}
