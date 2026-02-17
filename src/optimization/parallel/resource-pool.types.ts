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

export type ResourceType =
  | 'cpu_core'
  | 'memory_block'
  | 'io_channel'
  | 'network_bandwidth'
  | 'worker_thread'
  | 'compute_unit';

export interface ResourceCapacity {
  value: number;
  unit: string;
  scalable: boolean;
  maxScale: number;
}

export type ResourceStatus =
  | 'available'
  | 'allocated'
  | 'reserved'
  | 'maintenance'
  | 'failed'
  | 'scaling';

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

export type AllocationAlgorithm =
  | 'first_fit'
  | 'best_fit'
  | 'worst_fit'
  | 'buddy_system'
  | 'slab_allocation'
  | 'smart_placement';

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
