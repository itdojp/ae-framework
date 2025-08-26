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
  interval: number; // Aggregation interval in milliseconds
  functions: AggregationFunction[];
  retention: number; // How long to keep aggregated data
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

export class MetricsCollector extends EventEmitter {
  private metrics = new Map<string, MetricSeries>();
  private aggregations = new Map<string, AggregatedMetric[]>();
  private config: AggregationConfig;
  private aggregationTimer?: NodeJS.Timeout;
  private exportConfigs: MetricsExportConfig[] = [];
  private isCollecting = false;

  constructor(config: Partial<AggregationConfig> = {}) {
    super();
    this.config = {
      interval: 60000, // 1 minute
      functions: ['avg', 'min', 'max', 'p95'],
      retention: 3600000, // 1 hour
      ...config
    };
  }

  /**
   * Start metrics collection
   */
  start(): void {
    if (this.isCollecting) {
      return;
    }

    this.isCollecting = true;
    this.startAggregation();
    this.emit('collectionStarted');
    console.log('📊 Metrics collection started');
  }

  /**
   * Stop metrics collection
   */
  stop(): void {
    if (!this.isCollecting) {
      return;
    }

    this.isCollecting = false;
    
    if (this.aggregationTimer) {
      clearInterval(this.aggregationTimer);
      this.aggregationTimer = undefined;
    }

    this.emit('collectionStopped');
    console.log('📊 Metrics collection stopped');
  }

  /**
   * Record a single metric point
   */
  recordMetric(
    name: string,
    value: number,
    tags: Record<string, string> = {},
    unit = '',
    type: MetricPoint['type'] = 'gauge'
  ): void {
    const point: MetricPoint = {
      name,
      value,
      timestamp: new Date(),
      tags,
      unit,
      type
    };

    this.addMetricPoint(point);
    this.emit('metricRecorded', point);
  }

  /**
   * Record multiple metrics from performance data
   */
  recordPerformanceMetrics(perfMetrics: PerformanceMetrics): void {
    const timestamp = perfMetrics.timestamp;
    const commonTags = { source: 'performance-monitor' };

    // CPU metrics
    this.recordMetricWithTimestamp('cpu.user', perfMetrics.cpuUsage.userCPU, timestamp, commonTags, '%', 'gauge');
    this.recordMetricWithTimestamp('cpu.system', perfMetrics.cpuUsage.systemCPU, timestamp, commonTags, '%', 'gauge');
    this.recordMetricWithTimestamp('cpu.total', perfMetrics.cpuUsage.totalUsage, timestamp, commonTags, '%', 'gauge');
    const loadAvg1m = perfMetrics.cpuUsage.loadAverage?.[0];
    if (typeof loadAvg1m === 'number') {
      this.recordMetricWithTimestamp('cpu.load_avg_1m', loadAvg1m, timestamp, commonTags, '', 'gauge');
    }

    // Memory metrics
    this.recordMetricWithTimestamp('memory.heap_used', perfMetrics.memoryUsage.heapUsed, timestamp, commonTags, 'bytes', 'gauge');
    this.recordMetricWithTimestamp('memory.heap_total', perfMetrics.memoryUsage.heapTotal, timestamp, commonTags, 'bytes', 'gauge');
    this.recordMetricWithTimestamp('memory.rss', perfMetrics.memoryUsage.rss, timestamp, commonTags, 'bytes', 'gauge');
    this.recordMetricWithTimestamp('memory.usage_percent', perfMetrics.memoryUsage.usagePercentage, timestamp, commonTags, '%', 'gauge');

    // Response time metrics
    this.recordMetricWithTimestamp('response_time.avg', perfMetrics.responseTime.average, timestamp, commonTags, 'ms', 'gauge');
    this.recordMetricWithTimestamp('response_time.p95', perfMetrics.responseTime.p95, timestamp, commonTags, 'ms', 'gauge');
    this.recordMetricWithTimestamp('response_time.p99', perfMetrics.responseTime.p99, timestamp, commonTags, 'ms', 'gauge');

    // Throughput metrics
    this.recordMetricWithTimestamp('throughput.requests_per_sec', perfMetrics.throughput.requestsPerSecond, timestamp, commonTags, 'req/s', 'gauge');
    this.recordMetricWithTimestamp('throughput.concurrent_tasks', perfMetrics.throughput.concurrentTasks, timestamp, commonTags, '', 'gauge');

    // Error metrics
    this.recordMetricWithTimestamp('errors.rate', perfMetrics.errorRate.errorRate, timestamp, commonTags, '%', 'gauge');
    this.recordMetricWithTimestamp('errors.total', perfMetrics.errorRate.totalErrors, timestamp, commonTags, '', 'counter');

    // Custom metrics
    Object.entries(perfMetrics.customMetrics).forEach(([key, value]) => {
      this.recordMetricWithTimestamp(`custom.${key}`, value, timestamp, commonTags, '', 'gauge');
    });
  }

  /**
   * Increment a counter metric
   */
  incrementCounter(name: string, value = 1, tags: Record<string, string> = {}): void {
    this.recordMetric(name, value, tags, '', 'counter');
  }

  /**
   * Set a gauge metric
   */
  setGauge(name: string, value: number, tags: Record<string, string> = {}): void {
    this.recordMetric(name, value, tags, '', 'gauge');
  }

  /**
   * Record a timer metric
   */
  recordTimer(name: string, duration: number, tags: Record<string, string> = {}): void {
    this.recordMetric(name, duration, tags, 'ms', 'timer');
  }

  /**
   * Record a histogram metric
   */
  recordHistogram(name: string, value: number, tags: Record<string, string> = {}): void {
    this.recordMetric(name, value, tags, '', 'histogram');
  }

  /**
   * Get metrics series by name
   */
  getMetricSeries(name: string): MetricSeries | undefined {
    return this.metrics.get(name);
  }

  /**
   * Get all metric series
   */
  getAllMetrics(): Map<string, MetricSeries> {
    return new Map(this.metrics);
  }

  /**
   * Get aggregated metrics for a time range
   */
  getAggregatedMetrics(
    name: string,
    startTime: Date,
    endTime: Date
  ): AggregatedMetric[] {
    const aggregations = this.aggregations.get(name) || [];
    return aggregations.filter(agg => 
      agg.timestamp >= startTime && agg.timestamp <= endTime
    );
  }

  /**
   * Query metrics with filters
   */
  queryMetrics(filter: MetricFilter): MetricPoint[] {
    const results: MetricPoint[] = [];

    for (const [name, series] of this.metrics) {
      if (filter.name && !name.includes(filter.name)) {
        continue;
      }

      for (const point of series.points) {
        // Check time range
        if (filter.timeRange) {
          if (point.timestamp < filter.timeRange.start || 
              point.timestamp > filter.timeRange.end) {
            continue;
          }
        }

        // Check tags
        if (filter.tags) {
          const matchesTags = Object.entries(filter.tags).every(
            ([key, value]) => point.tags[key] === value
          );
          if (!matchesTags) {
            continue;
          }
        }

        results.push(point);
      }
    }

    return results;
  }

  /**
   * Create a metrics snapshot
   */
  createSnapshot(): MetricsSnapshot {
    const allPoints: MetricPoint[] = [];
    const allAggregations: AggregatedMetric[] = [];
    const uniqueNames = new Set<string>();
    let minTime: Date | null = null;
    let maxTime: Date | null = null;

    // Collect all metric points
    for (const [name, series] of this.metrics) {
      uniqueNames.add(name);
      allPoints.push(...series.points);

      for (const point of series.points) {
        if (!minTime || point.timestamp < minTime) minTime = point.timestamp;
        if (!maxTime || point.timestamp > maxTime) maxTime = point.timestamp;
      }
    }

    // Collect all aggregations
    for (const aggregations of this.aggregations.values()) {
      allAggregations.push(...aggregations);
    }

    return {
      timestamp: new Date(),
      metrics: allPoints,
      aggregations: allAggregations,
      summary: {
        totalMetrics: allPoints.length,
        uniqueNames: uniqueNames.size,
        timeRange: {
          start: minTime || new Date(),
          end: maxTime || new Date()
        }
      }
    };
  }

  /**
   * Export metrics in specified format
   */
  exportMetrics(config: MetricsExportConfig): string {
    const snapshot = this.createSnapshot();
    
    switch (config.format) {
      case 'prometheus':
        return this.exportPrometheus(snapshot, config);
      case 'json':
        return this.exportJSON(snapshot, config);
      case 'csv':
        return this.exportCSV(snapshot, config);
      case 'influxdb':
        return this.exportInfluxDB(snapshot, config);
      default:
        throw new Error(`Unsupported export format: ${config.format}`);
    }
  }

  /**
   * Add export configuration
   */
  addExportConfig(config: MetricsExportConfig): void {
    this.exportConfigs.push(config);
    
    if (config.interval) {
      setInterval(() => {
        try {
          const exported = this.exportMetrics(config);
          this.emit('metricsExported', { config, data: exported });
        } catch (error) {
          this.emit('exportError', { config, error });
        }
      }, config.interval);
    }
  }

  /**
   * Clear all metrics
   */
  clearMetrics(): void {
    this.metrics.clear();
    this.aggregations.clear();
    this.emit('metricsCleared');
  }

  // Private methods
  private recordMetricWithTimestamp(
    name: string,
    value: number,
    timestamp: Date,
    tags: Record<string, string>,
    unit: string,
    type: MetricPoint['type']
  ): void {
    const point: MetricPoint = {
      name,
      value,
      timestamp,
      tags,
      unit,
      type
    };

    this.addMetricPoint(point);
  }

  private addMetricPoint(point: MetricPoint): void {
    if (!this.metrics.has(point.name)) {
      this.metrics.set(point.name, {
        name: point.name,
        points: [],
        metadata: {
          description: `Metric: ${point.name}`,
          unit: point.unit,
          type: point.type,
          retention: this.config.retention
        }
      });
    }

    const series = this.metrics.get(point.name)!;
    series.points.push(point);

    // Cleanup old points
    const cutoff = Date.now() - series.metadata.retention;
    series.points = series.points.filter(p => p.timestamp.getTime() > cutoff);
  }

  private startAggregation(): void {
    this.aggregationTimer = setInterval(() => {
      this.performAggregation();
    }, this.config.interval);
  }

  private performAggregation(): void {
    const windowEnd = new Date();
    const windowStart = new Date(windowEnd.getTime() - this.config.interval);

    for (const [name, series] of this.metrics) {
      const windowPoints = series.points.filter(
        p => p.timestamp >= windowStart && p.timestamp < windowEnd
      );

      if (windowPoints.length === 0) continue;

      const values = windowPoints.map(p => p.value);
      
      for (const func of this.config.functions) {
        const aggregatedValue = this.calculateAggregation(values, func);
        
        const aggregation: AggregatedMetric = {
          name,
          function: func,
          value: aggregatedValue,
          timestamp: windowEnd,
          windowStart,
          windowEnd,
          count: values.length
        };

        if (!this.aggregations.has(name)) {
          this.aggregations.set(name, []);
        }

        this.aggregations.get(name)!.push(aggregation);
        
        // Cleanup old aggregations
        const cutoff = Date.now() - this.config.retention;
        this.aggregations.set(name, 
          this.aggregations.get(name)!.filter(a => a.timestamp.getTime() > cutoff)
        );
      }
    }

    this.emit('aggregationCompleted', { windowStart, windowEnd });
  }

  private calculateAggregation(values: number[], func: AggregationFunction): number {
    if (values.length === 0) return 0;

    const sorted = [...values].sort((a, b) => a - b);

    switch (func) {
      case 'sum':
        return values.reduce((sum, val) => sum + val, 0);
      case 'avg':
        return values.reduce((sum, val) => sum + val, 0) / values.length;
      case 'min':
        return Math.min(...values);
      case 'max':
        return Math.max(...values);
      case 'count':
        return values.length;
      case 'p50':
        return sorted[Math.floor(sorted.length * 0.5)] ?? 0;
      case 'p95':
        return sorted[Math.floor(sorted.length * 0.95)] ?? 0;
      case 'p99':
        return sorted[Math.floor(sorted.length * 0.99)] ?? 0;
      default:
        return 0;
    }
  }

  private exportPrometheus(snapshot: MetricsSnapshot, config: MetricsExportConfig): string {
    const lines: string[] = [];
    const metricsByName = new Map<string, MetricPoint[]>();

    // Group metrics by name
    for (const point of snapshot.metrics) {
      if (!metricsByName.has(point.name)) {
        metricsByName.set(point.name, []);
      }
      metricsByName.get(point.name)!.push(point);
    }

    // Export each metric
    for (const [name, points] of metricsByName) {
      const sanitizedName = name.replace(/[^a-zA-Z0-9_]/g, '_');
      
      // Add HELP and TYPE
      lines.push(`# HELP ${sanitizedName} Metric: ${name}`);
      lines.push(`# TYPE ${sanitizedName} gauge`);

      // Add metric points
      for (const point of points) {
        const labels = config.includeLabels ? this.formatLabels(point.tags) : '';
        const value = isNaN(point.value) ? 0 : point.value;
        const timestamp = point.timestamp.getTime();
        lines.push(`${sanitizedName}${labels} ${value} ${timestamp}`);
      }

      lines.push('');
    }

    return lines.join('\n');
  }

  private exportJSON(snapshot: MetricsSnapshot, config: MetricsExportConfig): string {
    return JSON.stringify(snapshot, null, 2);
  }

  private exportCSV(snapshot: MetricsSnapshot, config: MetricsExportConfig): string {
    const headers = ['timestamp', 'name', 'value', 'unit', 'type'];
    if (config.includeLabels) {
      headers.push('tags');
    }

    const lines = [headers.join(',')];

    for (const point of snapshot.metrics) {
      const row = [
        point.timestamp.toISOString(),
        `"${point.name}"`,
        point.value.toString(),
        `"${point.unit}"`,
        `"${point.type}"`
      ];

      if (config.includeLabels) {
        row.push(`"${JSON.stringify(point.tags)}"`);
      }

      lines.push(row.join(','));
    }

    return lines.join('\n');
  }

  private exportInfluxDB(snapshot: MetricsSnapshot, config: MetricsExportConfig): string {
    const lines: string[] = [];

    for (const point of snapshot.metrics) {
      const measurement = point.name.replace(/[^a-zA-Z0-9_]/g, '_');
      const tags = config.includeLabels ? this.formatInfluxTags(point.tags) : '';
      const fields = `value=${point.value}`;
      const timestamp = point.timestamp.getTime() * 1000000; // nanoseconds

      lines.push(`${measurement}${tags} ${fields} ${timestamp}`);
    }

    return lines.join('\n');
  }

  private formatLabels(tags: Record<string, string>): string {
    const entries = Object.entries(tags);
    if (entries.length === 0) return '';
    
    const formatted = entries.map(([key, value]) => `${key}="${value}"`).join(',');
    return `{${formatted}}`;
  }

  private formatInfluxTags(tags: Record<string, string>): string {
    const entries = Object.entries(tags);
    if (entries.length === 0) return '';
    
    const formatted = entries.map(([key, value]) => `${key}=${value}`).join(',');
    return `,${formatted}`;
  }
}