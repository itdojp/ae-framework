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
export type { ParallelTask, TaskResult, ResourceRequirements, TaskPriority, TaskType, ResourceUsage, OptimizationStrategy, LoadBalancingStrategy, PriorityWeights, ResourceAllocationStrategy, AdaptiveScalingConfig, ParallelizationPlan, OptimizedTask, TaskGroup, ResourceUtilizationPlan, OptimizationMetrics } from './parallel-optimizer.js';
export type { ScheduledTask, SchedulingPolicy, SchedulingAlgorithm, PreemptionPolicy, PriorityBoostConfig, DeadlineHandling, FairnessConfig, SchedulingOptimization, SchedulingMetrics, TaskQueue, SchedulingDecision, ResourceAvailability } from './task-scheduler.js';
export type { PooledResource, ResourceType, ResourceCapacity, ResourceStatus, ResourceMetadata, ResourceConstraints, PerformanceMetrics, HealthCheckConfig, AllocationRecord, ResourceAllocation, PoolConfiguration, PoolStrategy, PoolSizing, AllocationPolicy, AllocationAlgorithm, PriorityHandling, FairnessPolicy, OverflowHandling, MonitoringConfig, AlertingConfig, OptimizationConfig, DefragmentationConfig, LoadBalancingConfig, CachingConfig, PredictionConfig, PoolMetrics } from './resource-pool.js';
/**
 * Create a complete parallel optimization system
 */
export declare class ParallelOptimizationSystem {
    private optimizer;
    private scheduler;
    private resourcePool;
    constructor(optimizerConfig?: any, schedulerConfig?: any, poolConfig?: any);
    /**
     * Start the complete system
     */
    start(): void;
    /**
     * Stop the complete system
     */
    stop(): Promise<void>;
    /**
     * Get the parallel optimizer
     */
    getOptimizer(): ParallelOptimizer;
    /**
     * Get the task scheduler
     */
    getScheduler(): TaskScheduler;
    /**
     * Get the resource pool
     */
    getResourcePool(): ResourcePool;
    /**
     * Get combined system metrics
     */
    getSystemMetrics(): {
        optimization: import("./parallel-optimizer.js").OptimizationMetrics;
        scheduling: import("./task-scheduler.js").SchedulingMetrics;
        resources: import("./resource-pool.js").PoolMetrics;
        timestamp: Date;
    };
    private setupIntegration;
    private getPriorityValue;
}
