/**
 * Resource Pool Management for Phase 3.3.2
 * Advanced resource allocation and pooling for parallel optimization
 */
import { EventEmitter } from 'events';
import type { ResourceRequirements } from './parallel-optimizer.js';
export interface PooledResource {
    id: string;
    type: ResourceType;
    capacity: ResourceCapacity;
    allocated: ResourceCapacity;
    available: ResourceCapacity;
    status: ResourceStatus;
    metadata: ResourceMetadata;
    lastUsed: Date;
    allocationHistory: AllocationRecord[];
}
export type ResourceType = 'cpu_core' | 'memory_block' | 'io_channel' | 'network_bandwidth' | 'worker_thread' | 'compute_unit';
export interface ResourceCapacity {
    value: number;
    unit: string;
    scalable: boolean;
    maxScale: number;
}
export type ResourceStatus = 'available' | 'allocated' | 'reserved' | 'maintenance' | 'failed' | 'scaling';
export interface ResourceMetadata {
    priority: number;
    affinityTags: string[];
    constraints: ResourceConstraints;
    performance: PerformanceMetrics;
    healthCheck: HealthCheckConfig;
}
export interface ResourceConstraints {
    minAllocation: number;
    maxAllocation: number;
    allocationGranularity: number;
    exclusiveAccess: boolean;
    coLocationRules: string[];
}
export interface PerformanceMetrics {
    throughput: number;
    latency: number;
    reliability: number;
    efficiency: number;
    lastBenchmark: Date;
}
export interface HealthCheckConfig {
    enabled: boolean;
    interval: number;
    timeout: number;
    retryCount: number;
    healthThreshold: number;
}
export interface AllocationRecord {
    taskId: string;
    allocatedAt: Date;
    releasedAt?: Date;
    duration?: number;
    allocation: ResourceCapacity;
    utilization: number;
}
export interface ResourceAllocation {
    id: string;
    taskId: string;
    resources: PooledResource[];
    allocation: ResourceRequirements;
    grantedAt: Date;
    expiresAt?: Date;
    priority: number;
    preemptable: boolean;
}
export interface PoolConfiguration {
    name: string;
    strategy: PoolStrategy;
    sizing: PoolSizing;
    allocation: AllocationPolicy;
    monitoring: MonitoringConfig;
    optimization: OptimizationConfig;
}
export type PoolStrategy = 'static' | 'dynamic' | 'elastic' | 'predictive' | 'hybrid';
export interface PoolSizing {
    initialSize: number;
    minSize: number;
    maxSize: number;
    scaleUpThreshold: number;
    scaleDownThreshold: number;
    scaleUpIncrement: number;
    scaleDownDecrement: number;
    cooldownPeriod: number;
}
export interface AllocationPolicy {
    algorithm: AllocationAlgorithm;
    priorityHandling: PriorityHandling;
    preemption: PreemptionPolicy;
    fairness: FairnessPolicy;
    overflow: OverflowHandling;
}
export type AllocationAlgorithm = 'first_fit' | 'best_fit' | 'worst_fit' | 'buddy_system' | 'slab_allocation' | 'smart_placement';
export interface PriorityHandling {
    enabled: boolean;
    levels: number;
    aging: boolean;
    agingFactor: number;
    starvationPrevention: boolean;
}
export interface PreemptionPolicy {
    enabled: boolean;
    strategy: 'priority_based' | 'lru' | 'resource_pressure' | 'deadline_aware';
    gracePeriod: number;
    notificationEnabled: boolean;
}
export interface FairnessPolicy {
    enabled: boolean;
    algorithm: 'proportional_share' | 'lottery' | 'stride_scheduling';
    weights: Record<string, number>;
    quotas: Record<string, number>;
}
export interface OverflowHandling {
    strategy: 'queue' | 'reject' | 'redirect' | 'degrade';
    maxQueueSize: number;
    timeout: number;
    fallbackPool?: string;
}
export interface MonitoringConfig {
    metricsCollection: boolean;
    healthChecking: boolean;
    performanceTracking: boolean;
    allocationTracking: boolean;
    alerting: AlertingConfig;
}
export interface AlertingConfig {
    enabled: boolean;
    thresholds: {
        utilization: number;
        availability: number;
        performance: number;
        errors: number;
    };
    channels: string[];
}
export interface OptimizationConfig {
    defragmentation: DefragmentationConfig;
    loadBalancing: LoadBalancingConfig;
    caching: CachingConfig;
    prediction: PredictionConfig;
}
export interface DefragmentationConfig {
    enabled: boolean;
    threshold: number;
    algorithm: 'compact' | 'relocate' | 'merge';
    schedule: string;
}
export interface LoadBalancingConfig {
    enabled: boolean;
    algorithm: 'round_robin' | 'least_used' | 'resource_aware' | 'locality_aware';
    rebalanceThreshold: number;
    migrationCost: number;
}
export interface CachingConfig {
    enabled: boolean;
    size: number;
    ttl: number;
    evictionPolicy: 'lru' | 'lfu' | 'fifo' | 'random';
}
export interface PredictionConfig {
    enabled: boolean;
    algorithm: 'linear_regression' | 'arima' | 'neural_network';
    windowSize: number;
    accuracy: number;
}
export interface PoolMetrics {
    totalResources: number;
    availableResources: number;
    allocatedResources: number;
    utilizationRate: number;
    allocationRate: number;
    fragmentationRatio: number;
    averageAllocationTime: number;
    successfulAllocations: number;
    failedAllocations: number;
    preemptions: number;
    defragmentations: number;
}
export declare class ResourcePool extends EventEmitter {
    private config;
    private resources;
    private allocations;
    private waitingQueue;
    private metrics;
    private isRunning;
    private maintenanceTimer?;
    private monitoringTimer?;
    constructor(config?: Partial<PoolConfiguration>);
    /**
     * Start the resource pool
     */
    start(): void;
    /**
     * Stop the resource pool
     */
    stop(): void;
    /**
     * Allocate resources for a task
     */
    allocateResources(taskId: string, requirements: ResourceRequirements, priority?: number): Promise<ResourceAllocation>;
    /**
     * Release resources for a task
     */
    releaseResources(allocationId: string): boolean;
    /**
     * Get current pool metrics
     */
    getPoolMetrics(): PoolMetrics;
    /**
     * Get resource utilization
     */
    getResourceUtilization(): Record<ResourceType, number>;
    /**
     * Add resources to the pool
     */
    addResource(resource: PooledResource): void;
    /**
     * Remove resource from the pool
     */
    removeResource(resourceId: string): boolean;
    /**
     * Update pool configuration
     */
    updateConfiguration(updates: Partial<PoolConfiguration>): void;
    /**
     * Get current allocation status
     */
    getAllocationStatus(): Array<{
        taskId: string;
        allocation: ResourceAllocation;
        utilization: number;
        duration: number;
    }>;
    /**
     * Force defragmentation
     */
    defragment(): Promise<void>;
    private createDefaultConfiguration;
    private initializeMetrics;
    private initializePool;
    private createResource;
    private tryAllocate;
    private selectResources;
    private bestFitSelection;
    private firstFitSelection;
    private worstFitSelection;
    private canSatisfyRequirements;
    private allocateResource;
    private releaseResource;
    private shouldHandleOverflow;
    private handleOverflow;
    private degradeRequirements;
    private sortWaitingQueue;
    private processWaitingQueue;
    private releaseAllAllocations;
    private calculateAllocationUtilization;
    private startMaintenance;
    private startMonitoring;
    private performMaintenance;
    private cleanupExpiredAllocations;
    private shouldDefragment;
    private performDefragmentation;
    private autoScale;
    private scaleUp;
    private scaleDown;
    private updateMetrics;
    private calculateFragmentationRatio;
    private checkHealthStatus;
    private performHealthCheck;
    private checkAlerts;
    private applyConfigurationChanges;
}
