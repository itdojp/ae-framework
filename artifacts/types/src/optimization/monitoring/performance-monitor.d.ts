/**
 * Performance Monitor for Phase 3.3 Optimization
 * Provides real-time performance monitoring and analysis
 */
import { EventEmitter } from 'events';
export interface PerformanceMetrics {
    timestamp: Date;
    cpuUsage: CPUMetrics;
    memoryUsage: MemoryMetrics;
    responseTime: ResponseTimeMetrics;
    throughput: ThroughputMetrics;
    errorRate: ErrorRateMetrics;
    customMetrics: Record<string, number>;
}
export interface CPUMetrics {
    userCPU: number;
    systemCPU: number;
    totalUsage: number;
    loadAverage: number[];
}
export interface MemoryMetrics {
    heapUsed: number;
    heapTotal: number;
    external: number;
    rss: number;
    buffers: number;
    cached: number;
    available: number;
    usagePercentage: number;
}
export interface ResponseTimeMetrics {
    average: number;
    median: number;
    p95: number;
    p99: number;
    min: number;
    max: number;
    samples: number[];
}
export interface ThroughputMetrics {
    requestsPerSecond: number;
    operationsPerSecond: number;
    tasksCompleted: number;
    concurrentTasks: number;
}
export interface ErrorRateMetrics {
    totalErrors: number;
    errorRate: number;
    errorsByType: Record<string, number>;
    criticalErrors: number;
}
export interface PerformanceAlert {
    id: string;
    type: 'warning' | 'critical' | 'info';
    category: 'cpu' | 'memory' | 'response_time' | 'error_rate' | 'custom';
    message: string;
    threshold: number;
    currentValue: number;
    timestamp: Date;
    recommendations: string[];
}
export interface MonitoringConfig {
    interval: number;
    thresholds: {
        cpu: {
            warning: number;
            critical: number;
        };
        memory: {
            warning: number;
            critical: number;
        };
        responseTime: {
            warning: number;
            critical: number;
        };
        errorRate: {
            warning: number;
            critical: number;
        };
    };
    enabledMetrics: {
        cpu: boolean;
        memory: boolean;
        responseTime: boolean;
        throughput: boolean;
        errorRate: boolean;
        custom: boolean;
    };
    retentionPeriod: number;
    alertCooldown: number;
}
export interface PerformanceBaseline {
    cpu: {
        normal: number;
        peak: number;
    };
    memory: {
        normal: number;
        peak: number;
    };
    responseTime: {
        normal: number;
        acceptable: number;
    };
    throughput: {
        minimum: number;
        optimal: number;
    };
    errorRate: {
        acceptable: number;
        critical: number;
    };
}
export declare class PerformanceMonitor extends EventEmitter {
    private config;
    private isMonitoring;
    private metrics;
    private alerts;
    private baseline;
    private monitoringTimer?;
    private performanceObserver?;
    private responseTimes;
    private operationCounts;
    private errorCounts;
    private lastAlerts;
    constructor(config?: Partial<MonitoringConfig>);
    /**
     * Start performance monitoring
     */
    start(): void;
    /**
     * Stop performance monitoring
     */
    stop(): void;
    /**
     * Collect current performance metrics
     */
    private collectMetrics;
    /**
     * Get CPU usage metrics
     */
    private getCPUMetrics;
    /**
     * Get memory usage metrics
     */
    private getMemoryMetrics;
    /**
     * Get response time metrics
     */
    private getResponseTimeMetrics;
    /**
     * Get throughput metrics
     */
    private getThroughputMetrics;
    /**
     * Get error rate metrics
     */
    private getErrorRateMetrics;
    /**
     * Get custom metrics
     */
    private getCustomMetrics;
    /**
     * Check thresholds and generate alerts
     */
    private checkThresholds;
    /**
     * Check CPU thresholds
     */
    private checkCPUThresholds;
    /**
     * Check memory thresholds
     */
    private checkMemoryThresholds;
    /**
     * Check response time thresholds
     */
    private checkResponseTimeThresholds;
    /**
     * Check error rate thresholds
     */
    private checkErrorRateThresholds;
    /**
     * Create a performance alert
     */
    private createAlert;
    /**
     * Process and emit alert
     */
    private processAlert;
    /**
     * Track operation for performance monitoring
     */
    trackOperation(operationName: string, startTime: number): void;
    /**
     * Track error for monitoring
     */
    trackError(errorType: string): void;
    /**
     * Set performance baseline
     */
    setBaseline(baseline: PerformanceBaseline): void;
    /**
     * Get current metrics
     */
    getCurrentMetrics(): PerformanceMetrics | null;
    /**
     * Get metrics history
     */
    getMetricsHistory(limit?: number): PerformanceMetrics[];
    /**
     * Get recent alerts
     */
    getRecentAlerts(limit?: number): PerformanceAlert[];
    /**
     * Clear metrics and alerts
     */
    clearHistory(): void;
    private createDefaultConfig;
    private setupPerformanceObserver;
    private cleanupOldMetrics;
    private getLoadAverage;
    private getTotalSystemMemory;
    private getCurrentConcurrentTasks;
    private getActiveConnections;
    private getQueueSize;
    private getCacheHitRate;
}
