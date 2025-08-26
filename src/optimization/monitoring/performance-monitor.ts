/**
 * Performance Monitor for Phase 3.3 Optimization
 * Provides real-time performance monitoring and analysis
 */

import type { EventEmitter } from 'events';
import { performance, PerformanceObserver } from 'perf_hooks';
import os from 'node:os';

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
  interval: number; // Monitoring interval in milliseconds
  thresholds: {
    cpu: { warning: number; critical: number };
    memory: { warning: number; critical: number };
    responseTime: { warning: number; critical: number };
    errorRate: { warning: number; critical: number };
  };
  enabledMetrics: {
    cpu: boolean;
    memory: boolean;
    responseTime: boolean;
    throughput: boolean;
    errorRate: boolean;
    custom: boolean;
  };
  retentionPeriod: number; // Data retention in milliseconds
  alertCooldown: number; // Cooldown period for repeated alerts
}

export interface PerformanceBaseline {
  cpu: { normal: number; peak: number };
  memory: { normal: number; peak: number };
  responseTime: { normal: number; acceptable: number };
  throughput: { minimum: number; optimal: number };
  errorRate: { acceptable: number; critical: number };
}

export class PerformanceMonitor extends EventEmitter {
  private config: MonitoringConfig;
  private isMonitoring = false;
  private metrics: PerformanceMetrics[] = [];
  private alerts: PerformanceAlert[] = [];
  private baseline: PerformanceBaseline | null = null;
  private monitoringTimer?: NodeJS.Timeout;
  private performanceObserver?: PerformanceObserver;
  private responseTimes: number[] = [];
  private operationCounts = new Map<string, number>();
  private errorCounts = new Map<string, number>();
  private lastAlerts = new Map<string, Date>();

  constructor(config: Partial<MonitoringConfig> = {}) {
    super();
    this.config = this.createDefaultConfig(config);
    this.setupPerformanceObserver();
  }

  /**
   * Start performance monitoring
   */
  start(): void {
    if (this.isMonitoring) {
      console.warn('Performance monitoring is already running');
      return;
    }

    this.isMonitoring = true;
    this.emit('monitoringStarted');

    // Start periodic monitoring
    this.monitoringTimer = setInterval(() => {
      this.collectMetrics();
    }, this.config.interval);

    // Start performance observer
    if (this.performanceObserver) {
      this.performanceObserver.observe({ entryTypes: ['measure', 'resource'] });
    }

    console.log(`🔍 Performance monitoring started with ${this.config.interval}ms interval`);
  }

  /**
   * Stop performance monitoring
   */
  stop(): void {
    if (!this.isMonitoring) {
      return;
    }

    this.isMonitoring = false;
    
    if (this.monitoringTimer) {
      clearInterval(this.monitoringTimer);
      this.monitoringTimer = undefined;
    }

    if (this.performanceObserver) {
      this.performanceObserver.disconnect();
    }

    this.emit('monitoringStopped');
    console.log('📊 Performance monitoring stopped');
  }

  /**
   * Collect current performance metrics
   */
  private async collectMetrics(): Promise<void> {
    try {
      const metrics: PerformanceMetrics = {
        timestamp: new Date(),
        cpuUsage: await this.getCPUMetrics(),
        memoryUsage: this.getMemoryMetrics(),
        responseTime: this.getResponseTimeMetrics(),
        throughput: this.getThroughputMetrics(),
        errorRate: this.getErrorRateMetrics(),
        customMetrics: this.getCustomMetrics()
      };

      this.metrics.push(metrics);
      this.cleanupOldMetrics();
      
      // Check for alerts
      this.checkThresholds(metrics);
      
      this.emit('metricsCollected', metrics);

    } catch (error) {
      this.emit('monitoringError', error);
      console.error('Error collecting metrics:', error);
    }
  }

  /**
   * Get CPU usage metrics
   */
  private async getCPUMetrics(): Promise<CPUMetrics> {
    return new Promise((resolve) => {
      const startUsage = process.cpuUsage();
      const startTime = process.hrtime();

      // Measure CPU usage over a small interval
      setTimeout(() => {
        const endUsage = process.cpuUsage(startUsage);
        const endTime = process.hrtime(startTime);
        
        const elapsedTime = endTime[0] * 1e6 + endTime[1] / 1e3; // microseconds
        const userCPU = endUsage.user / elapsedTime * 100;
        const systemCPU = endUsage.system / elapsedTime * 100;

        resolve({
          userCPU,
          systemCPU,
          totalUsage: userCPU + systemCPU,
          loadAverage: this.getLoadAverage()
        });
      }, 100);
    });
  }

  /**
   * Get memory usage metrics
   */
  private getMemoryMetrics(): MemoryMetrics {
    const memUsage = process.memoryUsage();
    const totalMemory = this.getTotalSystemMemory();
    
    return {
      heapUsed: memUsage.heapUsed,
      heapTotal: memUsage.heapTotal,
      external: memUsage.external,
      rss: memUsage.rss,
      buffers: 0, // Simplified for Node.js
      cached: 0,  // Simplified for Node.js
      available: totalMemory - memUsage.rss,
      usagePercentage: (memUsage.rss / totalMemory) * 100
    };
  }

  /**
   * Get response time metrics
   */
  private getResponseTimeMetrics(): ResponseTimeMetrics {
    if (this.responseTimes.length === 0) {
      return {
        average: 0,
        median: 0,
        p95: 0,
        p99: 0,
        min: 0,
        max: 0,
        samples: []
      };
    }

    const sorted = [...this.responseTimes].sort((a, b) => a - b);
    const len = sorted.length;

    return {
      average: this.responseTimes.reduce((sum, rt) => sum + rt, 0) / len,
      median: sorted[Math.floor(len / 2)] ?? 0,
      p95: sorted[Math.floor(len * 0.95)] ?? 0,
      p99: sorted[Math.floor(len * 0.99)] ?? 0,
      min: sorted[0] ?? 0,
      max: sorted[len - 1] ?? 0,
      samples: [...this.responseTimes]
    };
  }

  /**
   * Get throughput metrics
   */
  private getThroughputMetrics(): ThroughputMetrics {
    const totalOperations = Array.from(this.operationCounts.values())
      .reduce((sum, count) => sum + count, 0);
    
    const timeWindow = this.config.interval / 1000; // Convert to seconds
    
    return {
      requestsPerSecond: totalOperations / timeWindow,
      operationsPerSecond: totalOperations / timeWindow,
      tasksCompleted: totalOperations,
      concurrentTasks: this.getCurrentConcurrentTasks()
    };
  }

  /**
   * Get error rate metrics
   */
  private getErrorRateMetrics(): ErrorRateMetrics {
    const totalErrors = Array.from(this.errorCounts.values())
      .reduce((sum, count) => sum + count, 0);
    
    const totalOperations = Array.from(this.operationCounts.values())
      .reduce((sum, count) => sum + count, 0);

    const errorsByType: Record<string, number> = {};
    this.errorCounts.forEach((count, type) => {
      errorsByType[type] = count;
    });

    return {
      totalErrors,
      errorRate: totalOperations > 0 ? (totalErrors / totalOperations) * 100 : 0,
      errorsByType,
      criticalErrors: errorsByType['critical'] || 0
    };
  }

  /**
   * Get custom metrics
   */
  private getCustomMetrics(): Record<string, number> {
    // Placeholder for custom metrics
    return {
      activeConnections: this.getActiveConnections(),
      queueSize: this.getQueueSize(),
      cacheHitRate: this.getCacheHitRate()
    };
  }

  /**
   * Check thresholds and generate alerts
   */
  private checkThresholds(metrics: PerformanceMetrics): void {
    const alerts: PerformanceAlert[] = [];

    // CPU threshold checks
    if (this.config.enabledMetrics.cpu) {
      const cpuAlert = this.checkCPUThresholds(metrics.cpuUsage);
      if (cpuAlert) alerts.push(cpuAlert);
    }

    // Memory threshold checks
    if (this.config.enabledMetrics.memory) {
      const memoryAlert = this.checkMemoryThresholds(metrics.memoryUsage);
      if (memoryAlert) alerts.push(memoryAlert);
    }

    // Response time threshold checks
    if (this.config.enabledMetrics.responseTime) {
      const responseAlert = this.checkResponseTimeThresholds(metrics.responseTime);
      if (responseAlert) alerts.push(responseAlert);
    }

    // Error rate threshold checks
    if (this.config.enabledMetrics.errorRate) {
      const errorAlert = this.checkErrorRateThresholds(metrics.errorRate);
      if (errorAlert) alerts.push(errorAlert);
    }

    // Process alerts
    for (const alert of alerts) {
      this.processAlert(alert);
    }
  }

  /**
   * Check CPU thresholds
   */
  private checkCPUThresholds(cpuMetrics: CPUMetrics): PerformanceAlert | null {
    const { warning, critical } = this.config.thresholds.cpu;
    const usage = cpuMetrics.totalUsage;

    if (usage >= critical) {
      return this.createAlert('critical', 'cpu', 
        `Critical CPU usage: ${usage.toFixed(1)}%`, critical, usage,
        [
          'Consider scaling resources',
          'Optimize CPU-intensive operations',
          'Enable parallel processing'
        ]
      );
    } else if (usage >= warning) {
      return this.createAlert('warning', 'cpu',
        `High CPU usage: ${usage.toFixed(1)}%`, warning, usage,
        [
          'Monitor for sustained high usage',
          'Review recent performance changes'
        ]
      );
    }

    return null;
  }

  /**
   * Check memory thresholds
   */
  private checkMemoryThresholds(memoryMetrics: MemoryMetrics): PerformanceAlert | null {
    const { warning, critical } = this.config.thresholds.memory;
    const usage = memoryMetrics.usagePercentage;

    if (usage >= critical) {
      return this.createAlert('critical', 'memory',
        `Critical memory usage: ${usage.toFixed(1)}%`, critical, usage,
        [
          'Free up memory immediately',
          'Check for memory leaks',
          'Restart if necessary'
        ]
      );
    } else if (usage >= warning) {
      return this.createAlert('warning', 'memory',
        `High memory usage: ${usage.toFixed(1)}%`, warning, usage,
        [
          'Monitor memory trends',
          'Consider garbage collection tuning'
        ]
      );
    }

    return null;
  }

  /**
   * Check response time thresholds
   */
  private checkResponseTimeThresholds(responseMetrics: ResponseTimeMetrics): PerformanceAlert | null {
    const { warning, critical } = this.config.thresholds.responseTime;
    const avgResponseTime = responseMetrics.average;

    if (avgResponseTime >= critical) {
      return this.createAlert('critical', 'response_time',
        `Critical response time: ${avgResponseTime.toFixed(1)}ms`, critical, avgResponseTime,
        [
          'Optimize slow operations',
          'Check database queries',
          'Review system bottlenecks'
        ]
      );
    } else if (avgResponseTime >= warning) {
      return this.createAlert('warning', 'response_time',
        `Slow response time: ${avgResponseTime.toFixed(1)}ms`, warning, avgResponseTime,
        [
          'Monitor performance trends',
          'Profile slow operations'
        ]
      );
    }

    return null;
  }

  /**
   * Check error rate thresholds
   */
  private checkErrorRateThresholds(errorMetrics: ErrorRateMetrics): PerformanceAlert | null {
    const { warning, critical } = this.config.thresholds.errorRate;
    const rate = errorMetrics.errorRate;

    if (rate >= critical) {
      return this.createAlert('critical', 'error_rate',
        `Critical error rate: ${rate.toFixed(1)}%`, critical, rate,
        [
          'Investigate error causes immediately',
          'Check system health',
          'Review recent deployments'
        ]
      );
    } else if (rate >= warning) {
      return this.createAlert('warning', 'error_rate',
        `High error rate: ${rate.toFixed(1)}%`, warning, rate,
        [
          'Monitor error patterns',
          'Review error logs'
        ]
      );
    }

    return null;
  }

  /**
   * Create a performance alert
   */
  private createAlert(
    type: PerformanceAlert['type'],
    category: PerformanceAlert['category'],
    message: string,
    threshold: number,
    currentValue: number,
    recommendations: string[]
  ): PerformanceAlert {
    return {
      id: `alert-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`,
      type,
      category,
      message,
      threshold,
      currentValue,
      timestamp: new Date(),
      recommendations
    };
  }

  /**
   * Process and emit alert
   */
  private processAlert(alert: PerformanceAlert): void {
    const alertKey = `${alert.category}-${alert.type}`;
    const lastAlert = this.lastAlerts.get(alertKey);
    const now = new Date();

    // Check cooldown period
    if (lastAlert && (now.getTime() - lastAlert.getTime()) < this.config.alertCooldown) {
      return;
    }

    this.alerts.push(alert);
    this.lastAlerts.set(alertKey, now);
    this.emit('performanceAlert', alert);

    console.warn(`🚨 Performance Alert [${alert.type.toUpperCase()}]: ${alert.message}`);
  }

  /**
   * Track operation for performance monitoring
   */
  trackOperation(operationName: string, startTime: number): void {
    const duration = performance.now() - startTime;
    this.responseTimes.push(duration);
    
    const currentCount = this.operationCounts.get(operationName) || 0;
    this.operationCounts.set(operationName, currentCount + 1);

    // Limit response time samples
    if (this.responseTimes.length > 1000) {
      this.responseTimes = this.responseTimes.slice(-500);
    }
  }

  /**
   * Track error for monitoring
   */
  trackError(errorType: string): void {
    const currentCount = this.errorCounts.get(errorType) || 0;
    this.errorCounts.set(errorType, currentCount + 1);
  }

  /**
   * Set performance baseline
   */
  setBaseline(baseline: PerformanceBaseline): void {
    this.baseline = baseline;
    this.emit('baselineSet', baseline);
  }

  /**
   * Get current metrics
   */
  getCurrentMetrics(): PerformanceMetrics | null {
    const lastMetric = this.metrics[this.metrics.length - 1];
    return lastMetric ?? null;
  }

  /**
   * Get metrics history
   */
  getMetricsHistory(limit?: number): PerformanceMetrics[] {
    return limit ? this.metrics.slice(-limit) : [...this.metrics];
  }

  /**
   * Get recent alerts
   */
  getRecentAlerts(limit = 10): PerformanceAlert[] {
    return this.alerts.slice(-limit);
  }

  /**
   * Clear metrics and alerts
   */
  clearHistory(): void {
    this.metrics = [];
    this.alerts = [];
    this.responseTimes = [];
    this.operationCounts.clear();
    this.errorCounts.clear();
    this.lastAlerts.clear();
    this.emit('historyCleared');
  }

  // Helper methods
  private createDefaultConfig(overrides: Partial<MonitoringConfig>): MonitoringConfig {
    return {
      interval: 5000, // 5 seconds
      thresholds: {
        cpu: { warning: 70, critical: 90 },
        memory: { warning: 80, critical: 95 },
        responseTime: { warning: 1000, critical: 3000 },
        errorRate: { warning: 5, critical: 10 }
      },
      enabledMetrics: {
        cpu: true,
        memory: true,
        responseTime: true,
        throughput: true,
        errorRate: true,
        custom: true
      },
      retentionPeriod: 3600000, // 1 hour
      alertCooldown: 300000, // 5 minutes
      ...overrides
    };
  }

  private setupPerformanceObserver(): void {
    if (typeof PerformanceObserver !== 'undefined') {
      this.performanceObserver = new PerformanceObserver((list) => {
        for (const entry of list.getEntries()) {
          if (entry.entryType === 'measure') {
            this.responseTimes.push(entry.duration);
          }
        }
      });
    }
  }

  private cleanupOldMetrics(): void {
    const cutoff = Date.now() - this.config.retentionPeriod;
    this.metrics = this.metrics.filter(m => m.timestamp.getTime() > cutoff);
    this.alerts = this.alerts.filter(a => a.timestamp.getTime() > cutoff);
  }

  private getLoadAverage(): number[] {
    try {
      return process.platform === 'win32' ? [0, 0, 0] : os.loadavg();
    } catch {
      return [0, 0, 0];
    }
  }

  private getTotalSystemMemory(): number {
    try {
      return os.totalmem();
    } catch {
      return 8 * 1024 * 1024 * 1024; // Default 8GB
    }
  }

  private getCurrentConcurrentTasks(): number {
    // Simplified implementation
    return Array.from(this.operationCounts.values()).reduce((sum, count) => sum + count, 0);
  }

  private getActiveConnections(): number {
    // Demo placeholder: returns simulated connection count
    // TODO: Implement actual connection tracking in production
    const simulatedCount = Math.floor(Math.random() * 100);
    console.debug(`[Demo] Simulated active connections: ${simulatedCount}`);
    return simulatedCount;
  }

  private getQueueSize(): number {
    // Demo placeholder: returns simulated queue size
    // TODO: Implement actual queue size tracking in production
    const simulatedSize = Math.floor(Math.random() * 50);
    console.debug(`[Demo] Simulated queue size: ${simulatedSize}`);
    return simulatedSize;
  }

  private getCacheHitRate(): number {
    // Demo placeholder: returns simulated cache hit rate
    // TODO: Implement actual cache hit rate tracking in production
    const simulatedRate = 85 + Math.random() * 10;
    console.debug(`[Demo] Simulated cache hit rate: ${simulatedRate.toFixed(1)}%`);
    return simulatedRate;
  }
}