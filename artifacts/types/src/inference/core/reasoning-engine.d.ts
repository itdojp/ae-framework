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
export declare class ReasoningEngine extends EventEmitter {
    private options;
    private sequentialStrategy;
    private parallelStrategy;
    private activeSessions;
    private resultCache;
    private metrics;
    constructor(options?: {
        maxConcurrentSessions?: number;
        defaultTimeout?: number;
        cacheSize?: number;
        cacheTTL?: number;
        enableMetrics?: boolean;
    });
    /**
     * Process a reasoning request
     */
    processRequest(request: ReasoningRequest): Promise<StrategyResult>;
    /**
     * Get current engine metrics
     */
    getMetrics(): EngineMetrics;
    /**
     * Clear all caches and reset metrics
     */
    reset(): void;
    /**
     * Register custom reasoning strategies
     */
    registerStrategy(mode: string, strategy: SequentialStrategy | ParallelStrategy): void;
    private validateRequest;
    private createSession;
    private executeStrategy;
    private selectAndExecuteStrategy;
    private executeAdaptiveStrategy;
    private executeHybridStrategy;
    private combineResults;
    private validateResult;
    private getCachedResult;
    private cacheResult;
    private generateCacheKey;
    private analyzeComplexity;
    private estimateDataSize;
    private hasParallelizableWork;
    private getCurrentMemoryUsage;
    private initializeMetrics;
    private updateMetrics;
    private performMaintenance;
}
