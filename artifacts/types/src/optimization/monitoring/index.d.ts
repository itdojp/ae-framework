/**
 * Phase 3.3 Monitoring System Integration
 * Combines performance monitoring, metrics collection, and alert management
 */
import { EventEmitter } from 'events';
import { type PerformanceMetrics } from './performance-monitor.js';
import { type MetricsSnapshot } from './metrics-collector.js';
import { type AlertInstance, type AlertSummary } from './alert-manager.js';
export interface MonitoringSystemConfig {
    performanceMonitor?: {
        interval?: number;
        thresholds?: {
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
export declare class MonitoringSystem extends EventEmitter {
    private performanceMonitor;
    private metricsCollector;
    private alertManager;
    private config;
    private startTime;
    private isRunning;
    private healthCheckTimer?;
    private exportTimer?;
    constructor(config?: MonitoringSystemConfig);
    /**
     * Start the complete monitoring system
     */
    start(): Promise<void>;
    /**
     * Stop the monitoring system
     */
    stop(): Promise<void>;
    /**
     * Get current system health status
     */
    getHealthStatus(): SystemHealthStatus;
    /**
     * Get monitoring dashboard data
     */
    getDashboard(): MonitoringDashboard;
    /**
     * Track custom operation for monitoring
     */
    trackOperation(operationName: string, startTime: number): void;
    /**
     * Track error for monitoring
     */
    trackError(errorType: string): void;
    /**
     * Record custom metric
     */
    recordMetric(name: string, value: number, tags?: Record<string, string>): void;
    /**
     * Export current metrics
     */
    exportMetrics(format?: 'json' | 'prometheus' | 'csv'): string;
    /**
     * Get performance metrics history
     */
    getPerformanceHistory(limit?: number): PerformanceMetrics[];
    /**
     * Get alert history
     */
    getAlertHistory(limit?: number): import("./alert-manager.js").AlertHistory[];
    /**
     * Get active alerts
     */
    getActiveAlerts(): AlertInstance[];
    /**
     * Get alert summary
     */
    getAlertSummary(): AlertSummary;
    /**
     * Force metrics collection (for testing)
     */
    forceMetricsCollection(): void;
    /**
     * Silence all alerts for a duration
     */
    silenceAllAlerts(duration: number): void;
    /**
     * Clear old data
     */
    cleanup(): void;
    private setupIntegration;
    private startHealthChecks;
    private startMetricsExport;
    private mergeDefaultConfig;
}
export * from './performance-monitor.js';
export * from './metrics-collector.js';
export * from './alert-manager.js';
export declare function createMonitoringSystem(config?: MonitoringSystemConfig): MonitoringSystem;
export declare function startDefaultMonitoring(): Promise<MonitoringSystem>;
