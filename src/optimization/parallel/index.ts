/**
 * Phase 3.3.2: Parallel Processing Optimization Engine
 * Export all parallel optimization components
 */

import { ParallelOptimizer } from './parallel-optimizer.js';
import { TaskScheduler } from './task-scheduler.js';
import { ResourcePool } from './resource-pool.js';

export { ParallelOptimizer } from './parallel-optimizer.js';
export { TaskScheduler } from './task-scheduler.js';
export { ResourcePool } from './resource-pool.js';

export type {
  // Parallel Optimizer types
  ParallelTask,
  TaskResult,
  ResourceRequirements,
  TaskPriority,
  TaskType,
  ResourceUsage,
  OptimizationStrategy,
  LoadBalancingStrategy,
  PriorityWeights,
  ResourceAllocationStrategy,
  AdaptiveScalingConfig,
  ParallelizationPlan,
  OptimizedTask,
  TaskGroup,
  ResourceUtilizationPlan,
  OptimizationMetrics
} from './parallel-optimizer.js';

export type {
  ScheduledTask,
  SchedulingPolicy,
  SchedulingAlgorithm,
  PreemptionPolicy,
  PriorityBoostConfig,
  DeadlineHandling,
  FairnessConfig,
  SchedulingOptimization,
  SchedulingMetrics,
  TaskQueue,
  SchedulingDecision,
  ResourceAvailability
} from './task-scheduler.js';

export type {
  PooledResource,
  ResourceType,
  ResourceCapacity,
  ResourceStatus,
  ResourceMetadata,
  ResourceConstraints,
  PerformanceMetrics,
  HealthCheckConfig,
  AllocationRecord,
  ResourceAllocation,
  PoolConfiguration,
  PoolStrategy,
  PoolSizing,
  AllocationPolicy,
  AllocationAlgorithm,
  PriorityHandling,
  FairnessPolicy,
  OverflowHandling,
  MonitoringConfig,
  AlertingConfig,
  OptimizationConfig,
  DefragmentationConfig,
  LoadBalancingConfig,
  CachingConfig,
  PredictionConfig,
  PoolMetrics
} from './resource-pool.js';

/**
 * Create a complete parallel optimization system
 */
export class ParallelOptimizationSystem {
  private optimizer: ParallelOptimizer;
  private scheduler: TaskScheduler;
  private resourcePool: ResourcePool;

  constructor(
    optimizerConfig?: any,
    schedulerConfig?: any,
    poolConfig?: any
  ) {
    this.resourcePool = new ResourcePool(poolConfig);
    this.scheduler = new TaskScheduler(schedulerConfig);
    this.optimizer = new ParallelOptimizer(optimizerConfig);

    this.setupIntegration();
  }

  /**
   * Start the complete system
   */
  start(): void {
    this.resourcePool.start();
    this.scheduler.start();
    this.optimizer.start();
    
    console.log('🚀 Parallel Optimization System started');
  }

  /**
   * Stop the complete system
   */
  async stop(): Promise<void> {
    await this.optimizer.stop();
    this.scheduler.stop();
    this.resourcePool.stop();
    
    console.log('🛑 Parallel Optimization System stopped');
  }

  /**
   * Get the parallel optimizer
   */
  getOptimizer(): ParallelOptimizer {
    return this.optimizer;
  }

  /**
   * Get the task scheduler
   */
  getScheduler(): TaskScheduler {
    return this.scheduler;
  }

  /**
   * Get the resource pool
   */
  getResourcePool(): ResourcePool {
    return this.resourcePool;
  }

  /**
   * Get combined system metrics
   */
  getSystemMetrics() {
    return {
      optimization: this.optimizer.getOptimizationMetrics(),
      scheduling: this.scheduler.getSchedulingMetrics(),
      resources: this.resourcePool.getPoolMetrics(),
      timestamp: new Date()
    };
  }

  private setupIntegration(): void {
    // Integrate optimizer with scheduler
    this.optimizer.on('taskSubmitted', (task) => {
      this.scheduler.scheduleTask(task).catch(console.error);
    });

    // Integrate scheduler with resource pool
    this.scheduler.on('taskStarted', async (event) => {
      try {
        await this.resourcePool.allocateResources(
          event.task.id,
          event.task.resourceRequirements,
          this.getPriorityValue(event.task.priority)
        );
      } catch (error) {
        console.error('Resource allocation failed:', error);
      }
    });

    this.scheduler.on('taskCompleted', (event) => {
      // Resource cleanup would happen here in a real implementation
      console.log(`✅ Task ${event.task.id} completed`);
    });

    // Cross-system event forwarding
    this.resourcePool.on('alert', (alert) => {
      console.warn('🚨 Resource Pool Alert:', alert);
    });

    this.scheduler.on('schedulingDecision', (decision) => {
      console.log(`📅 Scheduling Decision: ${decision.decision.action} for ${decision.task.name}`);
    });

    this.optimizer.on('planExecutionCompleted', (event) => {
      console.log(`🎯 Plan execution completed: ${event.results.length} tasks`);
    });
  }

  private getPriorityValue(priority: string): number {
    const priorityMap: Record<string, number> = {
      urgent: 5,
      high: 4,
      normal: 3,
      low: 2,
      background: 1
    };
    return priorityMap[priority] || 3;
  }
}