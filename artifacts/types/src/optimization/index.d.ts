/**
 * Phase 3.3: Complete Optimization System Integration
 * Combines monitoring, parallel processing, and resource management
 */
import { EventEmitter } from 'events';
import { MonitoringSystem, type MonitoringSystemConfig, type MonitoringDashboard } from './monitoring/index.js';
import { ParallelOptimizationSystem, type OptimizationMetrics } from './parallel/index.js';
export interface OptimizationSystemConfig {
    monitoring?: MonitoringSystemConfig;
    parallelOptimization?: {
        optimizer?: any;
        scheduler?: any;
        resourcePool?: any;
    };
    integration?: {
        autoStart?: boolean;
        crossSystemMetrics?: boolean;
        adaptiveOptimization?: boolean;
        performanceBasedScaling?: boolean;
    };
}
export interface SystemMetrics {
    timestamp: Date;
    monitoring: {
        healthStatus: string;
        activeAlerts: number;
        metricsCount: number;
        uptime: number;
    };
    optimization: OptimizationMetrics;
    integration: {
        crossSystemEfficiency: number;
        adaptiveOptimizations: number;
        resourceUtilization: number;
        systemStability: number;
    };
    performance: {
        overallThroughput: number;
        systemLatency: number;
        errorRate: number;
        scalabilityIndex: number;
    };
}
export interface OptimizationDashboard {
    timestamp: Date;
    systemStatus: 'optimal' | 'good' | 'degraded' | 'critical';
    monitoringDashboard: MonitoringDashboard;
    optimizationMetrics: OptimizationMetrics;
    systemMetrics: SystemMetrics;
    recommendations: SystemRecommendation[];
    alerts: SystemAlert[];
}
export interface SystemRecommendation {
    id: string;
    type: 'performance' | 'resource' | 'scaling' | 'configuration';
    priority: 'high' | 'medium' | 'low';
    title: string;
    description: string;
    impact: string;
    action: string;
    estimatedBenefit: number;
}
export interface SystemAlert {
    id: string;
    level: 'info' | 'warning' | 'error' | 'critical';
    source: 'monitoring' | 'optimization' | 'integration';
    message: string;
    timestamp: Date;
    data?: any;
}
export declare class OptimizationSystem extends EventEmitter {
    private monitoringSystem;
    private parallelOptimization;
    private config;
    private isRunning;
    private startTime;
    private integrationTimer?;
    private adaptiveTimer?;
    private systemAlerts;
    private recommendations;
    constructor(config?: OptimizationSystemConfig);
    /**
     * Start the complete optimization system
     */
    start(): Promise<void>;
    /**
     * Stop the complete optimization system
     */
    stop(): Promise<void>;
    /**
     * Get comprehensive system metrics
     */
    getSystemMetrics(): SystemMetrics;
    /**
     * Get comprehensive system dashboard
     */
    getDashboard(): OptimizationDashboard;
    /**
     * Get monitoring system
     */
    getMonitoringSystem(): MonitoringSystem;
    /**
     * Get parallel optimization system
     */
    getParallelOptimizationSystem(): ParallelOptimizationSystem;
    /**
     * Track operation across both systems
     */
    trackOperation(operationName: string, startTime: number): void;
    /**
     * Track error across both systems
     */
    trackError(errorType: string): void;
    /**
     * Apply system optimization recommendations
     */
    applyOptimizationRecommendations(): Promise<void>;
    /**
     * Export comprehensive system report
     */
    exportSystemReport(): string;
    private setupIntegration;
    private startIntegrationServices;
    private stopIntegrationServices;
    private handleMonitoringAlert;
    private performAdaptiveOptimization;
    private optimizeForCpuPressure;
    private optimizeForMemoryPressure;
    private generateSystemRecommendations;
    private applyRecommendation;
    private addSystemAlert;
    private updateIntegrationMetrics;
    private cleanupOldAlerts;
    private calculateCrossSystemEfficiency;
    private calculateOverallResourceUtilization;
    private calculateSystemStability;
    private calculateScalabilityIndex;
    private mergeDefaultConfig;
}
export type { MonitoringSystemConfig, SystemHealthStatus, PerformanceMetrics as MonitoringPerformanceMetrics, PerformanceAlert, MetricPoint, MetricsSnapshot, AlertInstance, AlertSummary } from './monitoring/index.js';
export { MonitoringSystem, PerformanceMonitor, MetricsCollector, AlertManager } from './monitoring/index.js';
export type { ParallelTask, TaskResult, ResourceRequirements, ResourceUsage, OptimizationStrategy, ParallelizationPlan, OptimizationMetrics, ScheduledTask, SchedulingPolicy, TaskQueue, SchedulingMetrics, PooledResource, ResourceType, ResourceCapacity, PerformanceMetrics as ParallelPerformanceMetrics, MonitoringConfig as ParallelMonitoringConfig } from './parallel/index.js';
export { ParallelOptimizer, TaskScheduler, ResourcePool, ParallelOptimizationSystem } from './parallel/index.js';
export declare function createOptimizationSystem(config?: OptimizationSystemConfig): OptimizationSystem;
export declare function startDefaultOptimizationSystem(): Promise<OptimizationSystem>;
