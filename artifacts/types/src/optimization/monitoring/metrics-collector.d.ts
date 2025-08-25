/**
 * Metrics Collector for Phase 3.3 Optimization
 * Collects, aggregates, and exports performance metrics
 */
import { EventEmitter } from 'events';
import type { PerformanceMetrics } from './performance-monitor.js';
export interface MetricPoint {
    name: string;
    value: number;
    timestamp: Date;
    tags: Record<string, string>;
    unit: string;
    type: 'counter' | 'gauge' | 'histogram' | 'timer';
}
export interface MetricSeries {
    name: string;
    points: MetricPoint[];
    metadata: {
        description: string;
        unit: string;
        type: string;
        retention: number;
    };
}
export interface AggregationConfig {
    interval: number;
    functions: AggregationFunction[];
    retention: number;
}
export type AggregationFunction = 'sum' | 'avg' | 'min' | 'max' | 'count' | 'p50' | 'p95' | 'p99';
export interface AggregatedMetric {
    name: string;
    function: AggregationFunction;
    value: number;
    timestamp: Date;
    windowStart: Date;
    windowEnd: Date;
    count: number;
}
export interface MetricsExportConfig {
    format: 'prometheus' | 'json' | 'csv' | 'influxdb';
    endpoint?: string;
    interval?: number;
    includeLabels: boolean;
    filters?: MetricFilter[];
}
export interface MetricFilter {
    name?: string;
    tags?: Record<string, string>;
    timeRange?: {
        start: Date;
        end: Date;
    };
}
export interface MetricsSnapshot {
    timestamp: Date;
    metrics: MetricPoint[];
    aggregations: AggregatedMetric[];
    summary: {
        totalMetrics: number;
        uniqueNames: number;
        timeRange: {
            start: Date;
            end: Date;
        };
    };
}
export declare class MetricsCollector extends EventEmitter {
    private metrics;
    private aggregations;
    private config;
    private aggregationTimer?;
    private exportConfigs;
    private isCollecting;
    constructor(config?: Partial<AggregationConfig>);
    /**
     * Start metrics collection
     */
    start(): void;
    /**
     * Stop metrics collection
     */
    stop(): void;
    /**
     * Record a single metric point
     */
    recordMetric(name: string, value: number, tags?: Record<string, string>, unit?: string, type?: MetricPoint['type']): void;
    /**
     * Record multiple metrics from performance data
     */
    recordPerformanceMetrics(perfMetrics: PerformanceMetrics): void;
    /**
     * Increment a counter metric
     */
    incrementCounter(name: string, value?: number, tags?: Record<string, string>): void;
    /**
     * Set a gauge metric
     */
    setGauge(name: string, value: number, tags?: Record<string, string>): void;
    /**
     * Record a timer metric
     */
    recordTimer(name: string, duration: number, tags?: Record<string, string>): void;
    /**
     * Record a histogram metric
     */
    recordHistogram(name: string, value: number, tags?: Record<string, string>): void;
    /**
     * Get metrics series by name
     */
    getMetricSeries(name: string): MetricSeries | undefined;
    /**
     * Get all metric series
     */
    getAllMetrics(): Map<string, MetricSeries>;
    /**
     * Get aggregated metrics for a time range
     */
    getAggregatedMetrics(name: string, startTime: Date, endTime: Date): AggregatedMetric[];
    /**
     * Query metrics with filters
     */
    queryMetrics(filter: MetricFilter): MetricPoint[];
    /**
     * Create a metrics snapshot
     */
    createSnapshot(): MetricsSnapshot;
    /**
     * Export metrics in specified format
     */
    exportMetrics(config: MetricsExportConfig): string;
    /**
     * Add export configuration
     */
    addExportConfig(config: MetricsExportConfig): void;
    /**
     * Clear all metrics
     */
    clearMetrics(): void;
    private recordMetricWithTimestamp;
    private addMetricPoint;
    private startAggregation;
    private performAggregation;
    private calculateAggregation;
    private exportPrometheus;
    private exportJSON;
    private exportCSV;
    private exportInfluxDB;
    private formatLabels;
    private formatInfluxTags;
}
