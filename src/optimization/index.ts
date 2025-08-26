/**
 * Phase 3.3: Complete Optimization System Integration
 * Combines monitoring, parallel processing, and resource management
 */

import type { EventEmitter } from 'events';
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

export class OptimizationSystem extends EventEmitter {
  private monitoringSystem: MonitoringSystem;
  private parallelOptimization: ParallelOptimizationSystem;
  private config: OptimizationSystemConfig;
  private isRunning = false;
  private startTime: Date;
  private integrationTimer?: NodeJS.Timeout;
  private adaptiveTimer?: NodeJS.Timeout;
  private systemAlerts: SystemAlert[] = [];
  private recommendations: SystemRecommendation[] = [];

  constructor(config: OptimizationSystemConfig = {}) {
    super();
    this.config = this.mergeDefaultConfig(config);
    this.startTime = new Date();

    // Initialize subsystems
    this.monitoringSystem = new MonitoringSystem(config.monitoring);
    this.parallelOptimization = new ParallelOptimizationSystem(
      config.parallelOptimization?.optimizer,
      config.parallelOptimization?.scheduler,
      config.parallelOptimization?.resourcePool
    );

    this.setupIntegration();
  }

  /**
   * Start the complete optimization system
   */
  async start(): Promise<void> {
    if (this.isRunning) {
      console.warn('Optimization system is already running');
      return;
    }

    console.log('🚀 Starting Phase 3.3 Complete Optimization System...');

    try {
      // Start subsystems in order
      await this.monitoringSystem.start();
      this.parallelOptimization.start();

      // Start integration services
      this.startIntegrationServices();

      this.isRunning = true;
      this.emit('systemStarted');

      console.log('✅ Complete Optimization System started successfully');
      console.log('📊 Monitoring system active');
      console.log('⚡ Parallel optimization active');
      console.log('🔗 System integration active');

      // Generate initial recommendations
      this.generateSystemRecommendations();

    } catch (error) {
      console.error('❌ Failed to start optimization system:', error);
      this.emit('systemError', error);
      throw error;
    }
  }

  /**
   * Stop the complete optimization system
   */
  async stop(): Promise<void> {
    if (!this.isRunning) {
      return;
    }

    console.log('🛑 Stopping complete optimization system...');

    try {
      // Stop integration services
      this.stopIntegrationServices();

      // Stop subsystems
      await this.parallelOptimization.stop();
      await this.monitoringSystem.stop();

      this.isRunning = false;
      this.emit('systemStopped');

      console.log('✅ Complete optimization system stopped');

    } catch (error) {
      console.error('❌ Error stopping optimization system:', error);
      this.emit('systemError', error);
      throw error;
    }
  }

  /**
   * Get comprehensive system metrics
   */
  getSystemMetrics(): SystemMetrics {
    const monitoringHealth = this.monitoringSystem.getHealthStatus();
    const optimizationMetrics = this.parallelOptimization.getSystemMetrics().optimization;
    
    // Calculate integration metrics
    const crossSystemEfficiency = this.calculateCrossSystemEfficiency();
    const resourceUtilization = this.calculateOverallResourceUtilization();
    const systemStability = this.calculateSystemStability();

    // Calculate performance metrics
    const overallThroughput = optimizationMetrics.throughput;
    const systemLatency = optimizationMetrics.averageExecutionTime;
    const errorRate = 1 - optimizationMetrics.successRate;
    const scalabilityIndex = this.calculateScalabilityIndex();

    return {
      timestamp: new Date(),
      monitoring: {
        healthStatus: monitoringHealth.overall,
        activeAlerts: monitoringHealth.metrics.activeAlerts,
        metricsCount: monitoringHealth.metrics.metricsCount,
        uptime: monitoringHealth.metrics.uptime
      },
      optimization: optimizationMetrics,
      integration: {
        crossSystemEfficiency,
        adaptiveOptimizations: this.recommendations.length,
        resourceUtilization,
        systemStability
      },
      performance: {
        overallThroughput,
        systemLatency,
        errorRate,
        scalabilityIndex
      }
    };
  }

  /**
   * Get comprehensive system dashboard
   */
  getDashboard(): OptimizationDashboard {
    const systemMetrics = this.getSystemMetrics();
    const monitoringDashboard = this.monitoringSystem.getDashboard();
    const optimizationMetrics = this.parallelOptimization.getSystemMetrics().optimization;

    // Determine overall system status
    let systemStatus: OptimizationDashboard['systemStatus'] = 'optimal';
    
    if (systemMetrics.integration.systemStability < 0.8 || systemMetrics.performance.errorRate > 0.1) {
      systemStatus = 'critical';
    } else if (systemMetrics.integration.systemStability < 0.9 || systemMetrics.performance.errorRate > 0.05) {
      systemStatus = 'degraded';
    } else if (systemMetrics.integration.resourceUtilization > 0.9) {
      systemStatus = 'good';
    }

    return {
      timestamp: new Date(),
      systemStatus,
      monitoringDashboard,
      optimizationMetrics,
      systemMetrics,
      recommendations: [...this.recommendations],
      alerts: [...this.systemAlerts]
    };
  }

  /**
   * Get monitoring system
   */
  getMonitoringSystem(): MonitoringSystem {
    return this.monitoringSystem;
  }

  /**
   * Get parallel optimization system
   */
  getParallelOptimizationSystem(): ParallelOptimizationSystem {
    return this.parallelOptimization;
  }

  /**
   * Track operation across both systems
   */
  trackOperation(operationName: string, startTime: number): void {
    this.monitoringSystem.trackOperation(operationName, startTime);
  }

  /**
   * Track error across both systems
   */
  trackError(errorType: string): void {
    this.monitoringSystem.trackError(errorType);
    this.addSystemAlert({
      id: `error-${Date.now()}`,
      level: 'error',
      source: 'integration',
      message: `Error tracked: ${errorType}`,
      timestamp: new Date()
    });
  }

  /**
   * Apply system optimization recommendations
   */
  async applyOptimizationRecommendations(): Promise<void> {
    const highPriorityRecommendations = this.recommendations
      .filter(r => r.priority === 'high')
      .slice(0, 3); // Apply top 3 high priority recommendations

    for (const recommendation of highPriorityRecommendations) {
      try {
        await this.applyRecommendation(recommendation);
        this.addSystemAlert({
          id: `optimization-${Date.now()}`,
          level: 'info',
          source: 'integration',
          message: `Applied optimization: ${recommendation.title}`,
          timestamp: new Date(),
          data: { recommendation }
        });
      } catch (error) {
        console.error(`Failed to apply recommendation ${recommendation.id}:`, error);
        this.addSystemAlert({
          id: `optimization-error-${Date.now()}`,
          level: 'warning',
          source: 'integration',
          message: `Failed to apply optimization: ${recommendation.title}`,
          timestamp: new Date(),
          data: { recommendation, error }
        });
      }
    }
  }

  /**
   * Export comprehensive system report
   */
  exportSystemReport(): string {
    const dashboard = this.getDashboard();
    
    return JSON.stringify({
      reportTimestamp: new Date(),
      systemOverview: {
        status: dashboard.systemStatus,
        uptime: Date.now() - this.startTime.getTime(),
        version: '3.3.0'
      },
      performance: dashboard.systemMetrics.performance,
      monitoring: {
        healthStatus: dashboard.monitoringDashboard.healthStatus,
        activeAlerts: dashboard.monitoringDashboard.activeAlerts.length,
        metricsSnapshot: dashboard.monitoringDashboard.metricsSnapshot.summary
      },
      optimization: {
        metrics: dashboard.optimizationMetrics,
        resourceUtilization: dashboard.systemMetrics.integration.resourceUtilization
      },
      recommendations: dashboard.recommendations,
      alerts: dashboard.alerts.slice(-10), // Last 10 alerts
      integration: dashboard.systemMetrics.integration
    }, null, 2);
  }

  // Private methods
  private setupIntegration(): void {
    // Connect monitoring alerts to optimization decisions
    this.monitoringSystem.on('alertTriggered', (alert) => {
      this.handleMonitoringAlert(alert);
    });

    // Connect optimization events to monitoring
    this.parallelOptimization.getOptimizer().on('taskCompleted', (event) => {
      this.monitoringSystem.recordMetric('optimization.tasks.completed', 1, {
        taskType: event.task.type,
        priority: event.task.priority
      });
    });

    this.parallelOptimization.getOptimizer().on('taskFailed', (event) => {
      this.monitoringSystem.trackError('optimization.task.failed');
    });

    // Connect resource pool events to monitoring
    this.parallelOptimization.getResourcePool().on('alert', (alert) => {
      this.addSystemAlert({
        id: `resource-${Date.now()}`,
        level: alert.type === 'high_utilization' ? 'warning' : 'info',
        source: 'optimization',
        message: `Resource alert: ${alert.type}`,
        timestamp: new Date(),
        data: alert
      });
    });

    // Cross-system optimization
    this.monitoringSystem.on('metricsUpdated', () => {
      if (this.config.integration?.adaptiveOptimization) {
        this.performAdaptiveOptimization();
      }
    });
  }

  private startIntegrationServices(): void {
    // Start integration monitoring
    this.integrationTimer = setInterval(() => {
      this.updateIntegrationMetrics();
      this.cleanupOldAlerts();
    }, 30000); // Every 30 seconds

    // Start adaptive optimization
    if (this.config.integration?.adaptiveOptimization) {
      this.adaptiveTimer = setInterval(() => {
        this.performAdaptiveOptimization();
        this.generateSystemRecommendations();
      }, 60000); // Every minute
    }
  }

  private stopIntegrationServices(): void {
    if (this.integrationTimer) {
      clearInterval(this.integrationTimer);
      this.integrationTimer = undefined;
    }

    if (this.adaptiveTimer) {
      clearInterval(this.adaptiveTimer);
      this.adaptiveTimer = undefined;
    }
  }

  private handleMonitoringAlert(alert: any): void {
    // Convert monitoring alert to system alert
    this.addSystemAlert({
      id: `monitoring-${alert.id}`,
      level: alert.severity === 'critical' ? 'critical' : 'warning',
      source: 'monitoring',
      message: alert.message,
      timestamp: new Date(),
      data: alert
    });

    // Trigger adaptive optimization based on alert type
    if (alert.category === 'cpu' && alert.type === 'critical') {
      this.optimizeForCpuPressure();
    } else if (alert.category === 'memory' && alert.type === 'critical') {
      this.optimizeForMemoryPressure();
    }
  }

  private performAdaptiveOptimization(): void {
    const systemMetrics = this.getSystemMetrics();
    
    // CPU-based optimization
    if (systemMetrics.performance.overallThroughput < 50) {
      this.recommendations.push({
        id: `cpu-opt-${Date.now()}`,
        type: 'performance',
        priority: 'high',
        title: 'Increase Parallel Workers',
        description: 'Low throughput detected, consider increasing worker count',
        impact: 'Improved task processing speed',
        action: 'Scale up parallel optimizer workers',
        estimatedBenefit: 0.3
      });
    }

    // Memory-based optimization
    if (systemMetrics.integration.resourceUtilization > 0.9) {
      this.recommendations.push({
        id: `memory-opt-${Date.now()}`,
        type: 'resource',
        priority: 'high',
        title: 'Resource Pool Optimization',
        description: 'High resource utilization detected',
        impact: 'Better resource distribution',
        action: 'Enable resource defragmentation',
        estimatedBenefit: 0.2
      });
    }
  }

  private optimizeForCpuPressure(): void {
    // Reduce parallel processing load
    const optimizer = this.parallelOptimization.getOptimizer();
    optimizer.updateStrategy({
      maxConcurrency: Math.max(2, Math.floor(optimizer.getOptimizationMetrics().activeWorkers * 0.7))
    });

    this.addSystemAlert({
      id: `cpu-optimization-${Date.now()}`,
      level: 'info',
      source: 'integration',
      message: 'Applied CPU pressure optimization',
      timestamp: new Date()
    });
  }

  private optimizeForMemoryPressure(): void {
    // Trigger resource cleanup
    this.parallelOptimization.getResourcePool().defragment();
    this.monitoringSystem.cleanup();

    this.addSystemAlert({
      id: `memory-optimization-${Date.now()}`,
      level: 'info',
      source: 'integration',
      message: 'Applied memory pressure optimization',
      timestamp: new Date()
    });
  }

  private generateSystemRecommendations(): void {
    const systemMetrics = this.getSystemMetrics();
    
    // Clear old recommendations
    this.recommendations = this.recommendations.filter(r => 
      Date.now() - new Date(r.id.split('-')[2]).getTime() < 300000 // Keep for 5 minutes
    );

    // Performance recommendations
    if (systemMetrics.performance.errorRate > 0.05) {
      this.recommendations.push({
        id: `error-rate-${Date.now()}`,
        type: 'performance',
        priority: 'high',
        title: 'Reduce Error Rate',
        description: 'Error rate is above acceptable threshold',
        impact: 'Improved system reliability',
        action: 'Review and improve error handling',
        estimatedBenefit: 0.4
      });
    }

    // Scaling recommendations
    if (systemMetrics.performance.scalabilityIndex < 0.7) {
      this.recommendations.push({
        id: `scaling-${Date.now()}`,
        type: 'scaling',
        priority: 'medium',
        title: 'Improve Scalability',
        description: 'System scalability could be improved',
        impact: 'Better handling of increased load',
        action: 'Enable adaptive scaling',
        estimatedBenefit: 0.25
      });
    }
  }

  private async applyRecommendation(recommendation: SystemRecommendation): Promise<void> {
    switch (recommendation.type) {
      case 'performance':
        if (recommendation.action.includes('workers')) {
          const optimizer = this.parallelOptimization.getOptimizer();
          const currentMetrics = optimizer.getOptimizationMetrics();
          optimizer.updateStrategy({
            maxConcurrency: Math.min(16, currentMetrics.activeWorkers + 2)
          });
        }
        break;
      
      case 'resource':
        if (recommendation.action.includes('defragmentation')) {
          await this.parallelOptimization.getResourcePool().defragment();
        }
        break;
      
      case 'scaling':
        if (recommendation.action.includes('adaptive')) {
          // Enable adaptive scaling if not already enabled
          const resourcePool = this.parallelOptimization.getResourcePool();
          resourcePool.updateConfiguration({
            optimization: {
              defragmentation: { enabled: true, threshold: 0.3, algorithm: 'compact', schedule: '*/5 * * * *' },
              loadBalancing: { enabled: true, algorithm: 'resource_aware', rebalanceThreshold: 0.2, migrationCost: 0.1 },
              caching: { enabled: true, size: 1000, ttl: 300000, evictionPolicy: 'lru' },
              prediction: { enabled: true, algorithm: 'linear_regression', windowSize: 100, accuracy: 0.8 }
            }
          });
        }
        break;
    }

    // Remove applied recommendation
    this.recommendations = this.recommendations.filter(r => r.id !== recommendation.id);
  }

  private addSystemAlert(alert: SystemAlert): void {
    this.systemAlerts.push(alert);
    this.emit('systemAlert', alert);
    
    // Keep only last 100 alerts
    if (this.systemAlerts.length > 100) {
      this.systemAlerts = this.systemAlerts.slice(-100);
    }
  }

  private updateIntegrationMetrics(): void {
    // Update cross-system metrics and emit events
    const metrics = this.getSystemMetrics();
    this.emit('integrationMetrics', metrics);
  }

  private cleanupOldAlerts(): void {
    const oneHourAgo = Date.now() - 3600000;
    this.systemAlerts = this.systemAlerts.filter(alert => 
      alert.timestamp.getTime() > oneHourAgo
    );
  }

  private calculateCrossSystemEfficiency(): number {
    const monitoringHealth = this.monitoringSystem.getHealthStatus();
    const optimizationMetrics = this.parallelOptimization.getSystemMetrics().optimization;
    
    const healthScore = monitoringHealth.overall === 'healthy' ? 1.0 : 
                       monitoringHealth.overall === 'degraded' ? 0.7 : 0.3;
    
    // Use resource utilization as a proxy for optimization efficiency if parallel efficiency is 0
    const optimizationScore = optimizationMetrics.parallelEfficiency > 0 
      ? optimizationMetrics.parallelEfficiency 
      : Math.min(0.8, optimizationMetrics.resourceUtilization + 0.3);
    
    return Math.max(0.2, (healthScore + optimizationScore) / 2);
  }

  private calculateOverallResourceUtilization(): number {
    const resourcePool = this.parallelOptimization.getResourcePool();
    const poolMetrics = resourcePool.getPoolMetrics();
    return poolMetrics.utilizationRate;
  }

  private calculateSystemStability(): number {
    const optimizationMetrics = this.parallelOptimization.getSystemMetrics().optimization;
    const monitoringHealth = this.monitoringSystem.getHealthStatus();
    
    // Base stability from optimization success rate
    const baseStability = optimizationMetrics.successRate;
    
    // Health factor from monitoring system
    const healthFactor = monitoringHealth.overall === 'healthy' ? 1.0 : 
                        monitoringHealth.overall === 'degraded' ? 0.8 : 0.5;
    
    // Alert penalty
    const criticalAlerts = this.systemAlerts.filter(a => a.level === 'critical').length;
    const warningAlerts = this.systemAlerts.filter(a => a.level === 'warning').length;
    const alertPenalty = Math.min(0.3, (criticalAlerts * 0.1) + (warningAlerts * 0.05));
    
    // Calculate combined stability (minimum of 0.1 to avoid zero values)
    const stability = Math.max(0.1, (baseStability * healthFactor) - alertPenalty);
    
    return Math.min(1.0, stability);
  }

  private calculateScalabilityIndex(): number {
    const optimizationMetrics = this.parallelOptimization.getSystemMetrics().optimization;
    const efficiency = optimizationMetrics.parallelEfficiency;
    const resourceUtilization = optimizationMetrics.resourceUtilization;
    
    return (efficiency + (1 - resourceUtilization)) / 2;
  }

  private mergeDefaultConfig(config: OptimizationSystemConfig): OptimizationSystemConfig {
    return {
      monitoring: config.monitoring || {},
      parallelOptimization: config.parallelOptimization || {},
      integration: {
        autoStart: true,
        crossSystemMetrics: true,
        adaptiveOptimization: true,
        performanceBasedScaling: true,
        ...config.integration
      }
    };
  }
}

// Export all types and components with explicit re-exports to avoid naming conflicts
export type { 
  MonitoringSystemConfig,
  SystemHealthStatus,
  PerformanceMetrics as MonitoringPerformanceMetrics,
  PerformanceAlert,
  MetricPoint,
  MetricsSnapshot,
  AlertInstance,
  AlertSummary
} from './monitoring/index.js';
export { MonitoringSystem, PerformanceMonitor, MetricsCollector, AlertManager } from './monitoring/index.js';

export type {
  ParallelTask,
  TaskResult,
  ResourceRequirements,
  ResourceUsage,
  OptimizationStrategy,
  ParallelizationPlan,
  OptimizationMetrics,
  ScheduledTask,
  SchedulingPolicy,
  TaskQueue,
  SchedulingMetrics,
  PooledResource,
  ResourceType,
  ResourceCapacity,
  PerformanceMetrics as ParallelPerformanceMetrics,
  MonitoringConfig as ParallelMonitoringConfig
} from './parallel/index.js';
export { ParallelOptimizer, TaskScheduler, ResourcePool, ParallelOptimizationSystem } from './parallel/index.js';

// Convenience function to create a complete optimization system
export function createOptimizationSystem(config?: OptimizationSystemConfig): OptimizationSystem {
  return new OptimizationSystem(config);
}

// Convenience function to start optimization system with default configuration
export async function startDefaultOptimizationSystem(): Promise<OptimizationSystem> {
  const system = createOptimizationSystem({
    integration: { autoStart: true, adaptiveOptimization: true }
  });
  
  await system.start();
  return system;
}