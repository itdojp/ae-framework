/**
 * Phase 3.3 Monitoring System Integration
 * Combines performance monitoring, metrics collection, and alert management
 */

import { EventEmitter } from 'events';
import { PerformanceMonitor, type PerformanceMetrics, type PerformanceAlert } from './performance-monitor.js';
import { MetricsCollector, type MetricPoint, type MetricsSnapshot } from './metrics-collector.js';
import { AlertManager, type AlertInstance, type AlertSummary } from './alert-manager.js';

export interface MonitoringSystemConfig {
  performanceMonitor?: {
    interval?: number;
    thresholds?: {
      cpu: { warning: number; critical: number };
      memory: { warning: number; critical: number };
      responseTime: { warning: number; critical: number };
      errorRate: { warning: number; critical: number };
    };
  };
  metricsCollector?: {
    aggregationInterval?: number;
    retention?: number;
  };
  alertManager?: {
    enabled?: boolean;
    defaultNotifications?: boolean;
  };
  integration?: {
    autoStart?: boolean;
    exportMetrics?: boolean;
    exportInterval?: number;
  };
}

export interface SystemHealthStatus {
  overall: 'healthy' | 'degraded' | 'critical';
  components: {
    performanceMonitor: 'running' | 'stopped' | 'error';
    metricsCollector: 'running' | 'stopped' | 'error';
    alertManager: 'running' | 'stopped' | 'error';
  };
  metrics: {
    uptime: number;
    lastUpdate: Date;
    metricsCount: number;
    activeAlerts: number;
  };
  issues: string[];
}

export interface MonitoringDashboard {
  timestamp: Date;
  healthStatus: SystemHealthStatus;
  currentMetrics: PerformanceMetrics | null;
  activeAlerts: AlertInstance[];
  alertSummary: AlertSummary;
  metricsSnapshot: MetricsSnapshot;
  systemStats: {
    totalOperations: number;
    avgResponseTime: number;
    errorRate: number;
    uptime: number;
  };
}

export class MonitoringSystem extends EventEmitter {
  private performanceMonitor: PerformanceMonitor;
  private metricsCollector: MetricsCollector;
  private alertManager: AlertManager;
  private config: MonitoringSystemConfig;
  private startTime: Date;
  private isRunning = false;
  private healthCheckTimer?: NodeJS.Timeout;
  private exportTimer?: NodeJS.Timeout;

  constructor(config: MonitoringSystemConfig = {}) {
    super();
    this.config = this.mergeDefaultConfig(config);
    this.startTime = new Date();

    // Initialize components
    this.performanceMonitor = new PerformanceMonitor(config.performanceMonitor);
    this.metricsCollector = new MetricsCollector(config.metricsCollector);
    this.alertManager = new AlertManager();

    this.setupIntegration();
  }

  /**
   * Start the complete monitoring system
   */
  async start(): Promise<void> {
    if (this.isRunning) {
      console.warn('Monitoring system is already running');
      return;
    }

    console.log('🚀 Starting Phase 3.3 Monitoring System...');

    try {
      // Start components in order
      this.metricsCollector.start();
      this.alertManager.start();
      this.performanceMonitor.start();

      // Start health checks
      this.startHealthChecks();

      // Start metrics export if configured
      if (this.config.integration?.exportMetrics) {
        this.startMetricsExport();
      }

      this.isRunning = true;
      this.emit('systemStarted');

      console.log('✅ Monitoring System started successfully');
      console.log('📊 Performance monitoring active');
      console.log('📈 Metrics collection active');
      console.log('🚨 Alert management active');

    } catch (error) {
      console.error('❌ Failed to start monitoring system:', error);
      this.emit('systemError', error);
      throw error;
    }
  }

  /**
   * Stop the monitoring system
   */
  async stop(): Promise<void> {
    if (!this.isRunning) {
      return;
    }

    console.log('🛑 Stopping monitoring system...');

    try {
      // Stop components
      this.performanceMonitor.stop();
      this.alertManager.stop();
      this.metricsCollector.stop();

      // Stop timers
      if (this.healthCheckTimer) {
        clearInterval(this.healthCheckTimer);
        this.healthCheckTimer = undefined;
      }

      if (this.exportTimer) {
        clearInterval(this.exportTimer);
        this.exportTimer = undefined;
      }

      this.isRunning = false;
      this.emit('systemStopped');

      console.log('✅ Monitoring system stopped');

    } catch (error) {
      console.error('❌ Error stopping monitoring system:', error);
      this.emit('systemError', error);
      throw error;
    }
  }

  /**
   * Get current system health status
   */
  getHealthStatus(): SystemHealthStatus {
    const currentMetrics = this.performanceMonitor.getCurrentMetrics();
    const activeAlerts = this.alertManager.getActiveAlerts();
    const metricsSnapshot = this.metricsCollector.createSnapshot();

    // Determine overall health
    let overall: SystemHealthStatus['overall'] = 'healthy';
    const issues: string[] = [];

    if (activeAlerts.some(a => a.severity === 'critical')) {
      overall = 'critical';
      issues.push('Critical alerts active');
    } else if (activeAlerts.some(a => a.severity === 'warning')) {
      overall = 'degraded';
      issues.push('Warning alerts active');
    }

    // Check component health
    if (currentMetrics?.cpuUsage?.totalUsage && currentMetrics.cpuUsage.totalUsage > 90) {
      overall = overall === 'healthy' ? 'degraded' : overall;
      issues.push('High CPU usage');
    }

    if (currentMetrics?.memoryUsage?.usagePercentage && currentMetrics.memoryUsage.usagePercentage > 90) {
      overall = overall === 'healthy' ? 'degraded' : overall;
      issues.push('High memory usage');
    }

    return {
      overall,
      components: {
        performanceMonitor: this.isRunning ? 'running' : 'stopped',
        metricsCollector: this.isRunning ? 'running' : 'stopped',
        alertManager: this.isRunning ? 'running' : 'stopped'
      },
      metrics: {
        uptime: Date.now() - this.startTime.getTime(),
        lastUpdate: new Date(),
        metricsCount: metricsSnapshot.summary.totalMetrics,
        activeAlerts: activeAlerts.length
      },
      issues
    };
  }

  /**
   * Get monitoring dashboard data
   */
  getDashboard(): MonitoringDashboard {
    const healthStatus = this.getHealthStatus();
    const currentMetrics = this.performanceMonitor.getCurrentMetrics();
    const activeAlerts = this.alertManager.getActiveAlerts();
    const alertSummary = this.alertManager.getAlertSummary();
    const metricsSnapshot = this.metricsCollector.createSnapshot();

    // Calculate system stats
    const uptime = Date.now() - this.startTime.getTime();
    const recentMetrics = this.performanceMonitor.getMetricsHistory(10);
    
    let avgResponseTime = 0;
    let errorRate = 0;
    let totalOperations = 0;

    if (recentMetrics.length > 0) {
      avgResponseTime = recentMetrics.reduce((sum, m) => sum + m.responseTime.average, 0) / recentMetrics.length;
      errorRate = recentMetrics.reduce((sum, m) => sum + m.errorRate.errorRate, 0) / recentMetrics.length;
      totalOperations = recentMetrics.reduce((sum, m) => sum + m.throughput.tasksCompleted, 0);
    }

    return {
      timestamp: new Date(),
      healthStatus,
      currentMetrics,
      activeAlerts,
      alertSummary,
      metricsSnapshot,
      systemStats: {
        totalOperations,
        avgResponseTime,
        errorRate,
        uptime
      }
    };
  }

  /**
   * Track custom operation for monitoring
   */
  trackOperation(operationName: string, startTime: number): void {
    this.performanceMonitor.trackOperation(operationName, startTime);
  }

  /**
   * Track error for monitoring
   */
  trackError(errorType: string): void {
    this.performanceMonitor.trackError(errorType);
  }

  /**
   * Record custom metric
   */
  recordMetric(name: string, value: number, tags?: Record<string, string>): void {
    this.metricsCollector.recordMetric(name, value, tags);
  }

  /**
   * Export current metrics
   */
  exportMetrics(format: 'json' | 'prometheus' | 'csv' = 'json'): string {
    return this.metricsCollector.exportMetrics({
      format,
      includeLabels: true
    });
  }

  /**
   * Get performance metrics history
   */
  getPerformanceHistory(limit?: number): PerformanceMetrics[] {
    return this.performanceMonitor.getMetricsHistory(limit);
  }

  /**
   * Get alert history
   */
  getAlertHistory(limit?: number) {
    return this.alertManager.getAlertHistory(limit);
  }

  /**
   * Get active alerts
   */
  getActiveAlerts(): AlertInstance[] {
    return this.alertManager.getActiveAlerts();
  }

  /**
   * Get alert summary
   */
  getAlertSummary(): AlertSummary {
    return this.alertManager.getAlertSummary();
  }

  /**
   * Force metrics collection (for testing)
   */
  forceMetricsCollection(): void {
    const currentMetrics = this.performanceMonitor.getCurrentMetrics();
    if (currentMetrics) {
      this.metricsCollector.recordPerformanceMetrics(currentMetrics);
    }
  }

  /**
   * Silence all alerts for a duration
   */
  silenceAllAlerts(duration: number): void {
    const activeAlerts = this.alertManager.getActiveAlerts();
    for (const alert of activeAlerts) {
      this.alertManager.silenceAlert(alert.id, duration);
    }
    console.log(`🔇 Silenced ${activeAlerts.length} alerts for ${duration}ms`);
  }

  /**
   * Clear old data
   */
  cleanup(): void {
    this.performanceMonitor.clearHistory();
    this.metricsCollector.clearMetrics();
    this.alertManager.clearResolvedAlerts();
    console.log('🧹 Monitoring system cleanup completed');
  }

  // Private methods
  private setupIntegration(): void {
    // Connect performance monitor to metrics collector
    this.performanceMonitor.on('metricsCollected', (metrics: PerformanceMetrics) => {
      this.metricsCollector.recordPerformanceMetrics(metrics);
      this.emit('metricsUpdated', metrics);
    });

    // Connect performance monitor to alert manager
    this.performanceMonitor.on('performanceAlert', (alert: PerformanceAlert) => {
      this.alertManager.processPerformanceAlert(alert);
      this.emit('alertTriggered', alert);
    });

    // Connect metrics collector to alert manager
    this.metricsCollector.on('metricRecorded', (metric: MetricPoint) => {
      this.alertManager.processMetric(metric);
    });

    // Forward alert events
    this.alertManager.on('alertFired', (alert: AlertInstance) => {
      this.emit('alertFired', alert);
    });

    this.alertManager.on('alertResolved', (alert: AlertInstance) => {
      this.emit('alertResolved', alert);
    });

    // Error handling
    this.performanceMonitor.on('monitoringError', (error) => {
      this.emit('componentError', { component: 'performanceMonitor', error });
    });

    this.metricsCollector.on('exportError', (error) => {
      this.emit('componentError', { component: 'metricsCollector', error });
    });
  }

  private startHealthChecks(): void {
    this.healthCheckTimer = setInterval(() => {
      const health = this.getHealthStatus();
      this.emit('healthCheck', health);

      if (health.overall === 'critical') {
        console.warn('🚨 System health is CRITICAL');
      } else if (health.overall === 'degraded') {
        console.warn('⚠️ System health is DEGRADED');
      }
    }, 60000); // Every minute
  }

  private startMetricsExport(): void {
    const interval = this.config.integration?.exportInterval || 300000; // 5 minutes
    
    this.exportTimer = setInterval(() => {
      try {
        const exported = this.exportMetrics('json');
        this.emit('metricsExported', exported);
      } catch (error) {
        this.emit('exportError', error);
      }
    }, interval);
  }

  private mergeDefaultConfig(config: MonitoringSystemConfig): MonitoringSystemConfig {
    return {
      performanceMonitor: {
        interval: 5000,
        thresholds: {
          cpu: { warning: 70, critical: 90 },
          memory: { warning: 80, critical: 95 },
          responseTime: { warning: 1000, critical: 3000 },
          errorRate: { warning: 5, critical: 10 }
        },
        ...config.performanceMonitor
      },
      metricsCollector: {
        aggregationInterval: 60000,
        retention: 3600000,
        ...config.metricsCollector
      },
      alertManager: {
        enabled: true,
        defaultNotifications: true,
        ...config.alertManager
      },
      integration: {
        autoStart: true,
        exportMetrics: false,
        exportInterval: 300000,
        ...config.integration
      }
    };
  }
}

// Export all types and classes
export * from './performance-monitor.js';
export * from './metrics-collector.js';
export * from './alert-manager.js';

// Create default monitoring system instance
export function createMonitoringSystem(config?: MonitoringSystemConfig): MonitoringSystem {
  return new MonitoringSystem(config);
}

// Convenience function to start monitoring with default configuration
export async function startDefaultMonitoring(): Promise<MonitoringSystem> {
  const system = createMonitoringSystem({
    integration: { autoStart: true }
  });
  
  await system.start();
  return system;
}