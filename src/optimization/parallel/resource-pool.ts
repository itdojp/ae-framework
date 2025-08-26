/**
 * Resource Pool Management for Phase 3.3.2
 * Advanced resource allocation and pooling for parallel optimization
 */

import { EventEmitter } from 'events';
import type { ResourceRequirements, ResourceUsage } from './parallel-optimizer.js';

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

export type PoolStrategy = 
  | 'static'
  | 'dynamic'
  | 'elastic'
  | 'predictive'
  | 'hybrid';

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

export class ResourcePool extends EventEmitter {
  private config: PoolConfiguration;
  private resources = new Map<string, PooledResource>();
  private allocations = new Map<string, ResourceAllocation>();
  private waitingQueue: Array<{
    requirements: ResourceRequirements;
    taskId: string;
    priority: number;
    timestamp: Date;
    resolve: (allocation: ResourceAllocation) => void;
    reject: (error: Error) => void;
  }> = [];
  private metrics: PoolMetrics;
  private isRunning = false;
  private maintenanceTimer?: NodeJS.Timeout;
  private monitoringTimer?: NodeJS.Timeout;

  constructor(config?: Partial<PoolConfiguration>) {
    super();
    this.config = this.createDefaultConfiguration(config);
    this.metrics = this.initializeMetrics();
    this.initializePool();
  }

  /**
   * Start the resource pool
   */
  start(): void {
    if (this.isRunning) {
      return;
    }

    this.isRunning = true;
    this.startMaintenance();
    this.startMonitoring();
    this.emit('poolStarted');
    
    console.log(`🏊‍♂️ Resource Pool '${this.config.name}' started with ${this.resources.size} resources`);
  }

  /**
   * Stop the resource pool
   */
  stop(): void {
    if (!this.isRunning) {
      return;
    }

    this.isRunning = false;
    
    if (this.maintenanceTimer) {
      clearInterval(this.maintenanceTimer);
      this.maintenanceTimer = undefined;
    }
    
    if (this.monitoringTimer) {
      clearInterval(this.monitoringTimer);
      this.monitoringTimer = undefined;
    }

    // Release all allocations
    this.releaseAllAllocations();
    
    this.emit('poolStopped');
    console.log(`🏊‍♂️ Resource Pool '${this.config.name}' stopped`);
  }

  /**
   * Allocate resources for a task
   */
  async allocateResources(taskId: string, requirements: ResourceRequirements, priority = 0): Promise<ResourceAllocation> {
    if (!this.isRunning) {
      throw new Error('Resource pool is not running');
    }

    this.emit('allocationRequested', { taskId, requirements, priority });

    // Try immediate allocation
    const allocation = this.tryAllocate(taskId, requirements, priority);
    if (allocation) {
      this.metrics.successfulAllocations++;
      this.emit('allocationGranted', allocation);
      return allocation;
    }

    // Check if we should handle overflow
    if (this.shouldHandleOverflow()) {
      return this.handleOverflow(taskId, requirements, priority);
    }

    // Queue the request
    return new Promise((resolve, reject) => {
      this.waitingQueue.push({
        requirements,
        taskId,
        priority,
        timestamp: new Date(),
        resolve,
        reject
      });

      this.sortWaitingQueue();
      this.emit('allocationQueued', { taskId, queuePosition: this.waitingQueue.length });

      // Set timeout if configured
      if (this.config.allocation.overflow.timeout > 0) {
        setTimeout(() => {
          const index = this.waitingQueue.findIndex(req => req.taskId === taskId);
          if (index !== -1) {
            this.waitingQueue.splice(index, 1);
            reject(new Error(`Allocation timeout for task ${taskId}`));
          }
        }, this.config.allocation.overflow.timeout);
      }
    });
  }

  /**
   * Release resources for a task
   */
  releaseResources(allocationId: string): boolean {
    const allocation = this.allocations.get(allocationId);
    if (!allocation) {
      return false;
    }

    // Release each resource
    for (const resource of allocation.resources) {
      this.releaseResource(resource.id, allocation.allocation);
    }

    this.allocations.delete(allocationId);
    this.metrics.allocatedResources--;
    
    this.emit('allocationReleased', allocation);
    
    // Process waiting queue
    this.processWaitingQueue();
    
    return true;
  }

  /**
   * Get current pool metrics
   */
  getPoolMetrics(): PoolMetrics {
    this.updateMetrics();
    return { ...this.metrics };
  }

  /**
   * Get resource utilization
   */
  getResourceUtilization(): Record<ResourceType, number> {
    const utilization: Record<string, number> = {};
    
    for (const resource of this.resources.values()) {
      if (!utilization[resource.type]) {
        utilization[resource.type] = 0;
      }
      
      const used = resource.capacity.value - resource.available.value;
      const usage = resource.capacity.value > 0 ? used / resource.capacity.value : 0;
      const currentUtilization = utilization[resource.type] ?? 0;
      utilization[resource.type] = Math.max(currentUtilization, usage);
    }
    
    return utilization as Record<ResourceType, number>;
  }

  /**
   * Add resources to the pool
   */
  addResource(resource: PooledResource): void {
    this.resources.set(resource.id, resource);
    this.metrics.totalResources++;
    this.metrics.availableResources++;
    
    this.emit('resourceAdded', resource);
    
    // Process waiting queue
    this.processWaitingQueue();
  }

  /**
   * Remove resource from the pool
   */
  removeResource(resourceId: string): boolean {
    const resource = this.resources.get(resourceId);
    if (!resource) {
      return false;
    }

    // Check if resource is allocated
    if (resource.status === 'allocated') {
      // Force release allocations using this resource
      for (const allocation of this.allocations.values()) {
        if (allocation.resources.some(r => r.id === resourceId)) {
          this.releaseResources(allocation.id);
        }
      }
    }

    this.resources.delete(resourceId);
    this.metrics.totalResources--;
    if (resource.status === 'available') {
      this.metrics.availableResources--;
    }
    
    this.emit('resourceRemoved', { resourceId, resource });
    return true;
  }

  /**
   * Update pool configuration
   */
  updateConfiguration(updates: Partial<PoolConfiguration>): void {
    this.config = { ...this.config, ...updates };
    this.emit('configurationUpdated', this.config);
    
    // Apply configuration changes
    this.applyConfigurationChanges();
  }

  /**
   * Get current allocation status
   */
  getAllocationStatus(): Array<{
    taskId: string;
    allocation: ResourceAllocation;
    utilization: number;
    duration: number;
  }> {
    const now = Date.now();
    
    return Array.from(this.allocations.values()).map(allocation => ({
      taskId: allocation.taskId,
      allocation,
      utilization: this.calculateAllocationUtilization(allocation),
      duration: now - allocation.grantedAt.getTime()
    }));
  }

  /**
   * Force defragmentation
   */
  async defragment(): Promise<void> {
    if (!this.config.optimization.defragmentation.enabled) {
      return;
    }

    this.emit('defragmentationStarted');
    
    try {
      await this.performDefragmentation();
      this.metrics.defragmentations++;
      this.emit('defragmentationCompleted');
    } catch (error) {
      this.emit('defragmentationError', error);
      throw error;
    }
  }

  // Private methods
  private createDefaultConfiguration(overrides?: Partial<PoolConfiguration>): PoolConfiguration {
    return {
      name: 'Default Resource Pool',
      strategy: 'dynamic',
      sizing: {
        initialSize: 10,
        minSize: 5,
        maxSize: 50,
        scaleUpThreshold: 0.8,
        scaleDownThreshold: 0.3,
        scaleUpIncrement: 2,
        scaleDownDecrement: 1,
        cooldownPeriod: 30000
      },
      allocation: {
        algorithm: 'best_fit',
        priorityHandling: {
          enabled: true,
          levels: 5,
          aging: true,
          agingFactor: 0.1,
          starvationPrevention: true
        },
        preemption: {
          enabled: true,
          strategy: 'priority_based',
          gracePeriod: 5000,
          notificationEnabled: true
        },
        fairness: {
          enabled: true,
          algorithm: 'proportional_share',
          weights: {},
          quotas: {}
        },
        overflow: {
          strategy: 'queue',
          maxQueueSize: 100,
          timeout: 30000
        }
      },
      monitoring: {
        metricsCollection: true,
        healthChecking: true,
        performanceTracking: true,
        allocationTracking: true,
        alerting: {
          enabled: true,
          thresholds: {
            utilization: 0.9,
            availability: 0.1,
            performance: 0.5,
            errors: 0.05
          },
          channels: ['console']
        }
      },
      optimization: {
        defragmentation: {
          enabled: true,
          threshold: 0.3,
          algorithm: 'compact',
          schedule: '0 */30 * * * *' // Every 30 minutes
        },
        loadBalancing: {
          enabled: true,
          algorithm: 'resource_aware',
          rebalanceThreshold: 0.2,
          migrationCost: 0.1
        },
        caching: {
          enabled: true,
          size: 1000,
          ttl: 300000, // 5 minutes
          evictionPolicy: 'lru'
        },
        prediction: {
          enabled: true,
          algorithm: 'linear_regression',
          windowSize: 100,
          accuracy: 0.8
        }
      },
      ...overrides
    };
  }

  private initializeMetrics(): PoolMetrics {
    return {
      totalResources: 0,
      availableResources: 0,
      allocatedResources: 0,
      utilizationRate: 0,
      allocationRate: 0,
      fragmentationRatio: 0,
      averageAllocationTime: 0,
      successfulAllocations: 0,
      failedAllocations: 0,
      preemptions: 0,
      defragmentations: 0
    };
  }

  private initializePool(): void {
    // Create initial resources based on configuration
    for (let i = 0; i < this.config.sizing.initialSize; i++) {
      const resource = this.createResource(i);
      this.resources.set(resource.id, resource);
    }
    
    this.metrics.totalResources = this.resources.size;
    this.metrics.availableResources = this.resources.size;
  }

  private createResource(index: number): PooledResource {
    const resourceId = `resource-${Date.now()}-${index}`;
    
    return {
      id: resourceId,
      type: 'compute_unit',
      capacity: {
        value: 1.0,
        unit: 'core',
        scalable: true,
        maxScale: 2.0
      },
      allocated: {
        value: 0,
        unit: 'core',
        scalable: true,
        maxScale: 2.0
      },
      available: {
        value: 1.0,
        unit: 'core',
        scalable: true,
        maxScale: 2.0
      },
      status: 'available',
      metadata: {
        priority: 1,
        affinityTags: [],
        constraints: {
          minAllocation: 0.1,
          maxAllocation: 1.0,
          allocationGranularity: 0.1,
          exclusiveAccess: false,
          coLocationRules: []
        },
        performance: {
          throughput: 1.0,
          latency: 10,
          reliability: 0.99,
          efficiency: 0.85,
          lastBenchmark: new Date()
        },
        healthCheck: {
          enabled: true,
          interval: 30000,
          timeout: 5000,
          retryCount: 3,
          healthThreshold: 0.8
        }
      },
      lastUsed: new Date(),
      allocationHistory: []
    };
  }

  private tryAllocate(taskId: string, requirements: ResourceRequirements, priority: number): ResourceAllocation | null {
    const selectedResources = this.selectResources(requirements);
    if (!selectedResources || selectedResources.length === 0) {
      return null;
    }

    // Create allocation
    const allocationId = `alloc-${Date.now()}-${taskId}`;
    const allocation: ResourceAllocation = {
      id: allocationId,
      taskId,
      resources: selectedResources,
      allocation: requirements,
      grantedAt: new Date(),
      priority,
      preemptable: priority < 3 // Lower priority tasks are preemptable
    };

    // Allocate resources
    for (const resource of selectedResources) {
      this.allocateResource(resource.id, requirements);
    }

    this.allocations.set(allocationId, allocation);
    this.metrics.allocatedResources++;
    
    return allocation;
  }

  private selectResources(requirements: ResourceRequirements): PooledResource[] | null {
    const algorithm = this.config.allocation.algorithm;
    
    switch (algorithm) {
      case 'best_fit':
        return this.bestFitSelection(requirements);
      case 'first_fit':
        return this.firstFitSelection(requirements);
      case 'worst_fit':
        return this.worstFitSelection(requirements);
      default:
        return this.bestFitSelection(requirements);
    }
  }

  private bestFitSelection(requirements: ResourceRequirements): PooledResource[] | null {
    const availableResources = Array.from(this.resources.values())
      .filter(r => r.status === 'available' && this.canSatisfyRequirements(r, requirements));

    if (availableResources.length === 0) {
      return null;
    }

    // Sort by best fit (smallest sufficient resource)
    availableResources.sort((a, b) => {
      const aWaste = a.available.value - requirements.cpu;
      const bWaste = b.available.value - requirements.cpu;
      return aWaste - bWaste;
    });

    return [availableResources[0]];
  }

  private firstFitSelection(requirements: ResourceRequirements): PooledResource[] | null {
    for (const resource of this.resources.values()) {
      if (resource.status === 'available' && this.canSatisfyRequirements(resource, requirements)) {
        return [resource];
      }
    }
    return null;
  }

  private worstFitSelection(requirements: ResourceRequirements): PooledResource[] | null {
    const availableResources = Array.from(this.resources.values())
      .filter(r => r.status === 'available' && this.canSatisfyRequirements(r, requirements));

    if (availableResources.length === 0) {
      return null;
    }

    // Sort by worst fit (largest available resource)
    availableResources.sort((a, b) => b.available.value - a.available.value);

    return [availableResources[0]];
  }

  private canSatisfyRequirements(resource: PooledResource, requirements: ResourceRequirements): boolean {
    return resource.available.value >= requirements.cpu &&
           resource.metadata.constraints.minAllocation <= requirements.cpu &&
           resource.metadata.constraints.maxAllocation >= requirements.cpu;
  }

  private allocateResource(resourceId: string, requirements: ResourceRequirements): void {
    const resource = this.resources.get(resourceId);
    if (!resource) return;

    resource.allocated.value += requirements.cpu;
    resource.available.value -= requirements.cpu;
    resource.status = resource.available.value > 0 ? 'allocated' : 'allocated';
    resource.lastUsed = new Date();

    // Add allocation record
    resource.allocationHistory.push({
      taskId: `task-${Date.now()}`,
      allocatedAt: new Date(),
      allocation: {
        value: requirements.cpu,
        unit: 'core',
        scalable: false,
        maxScale: requirements.cpu
      },
      utilization: 0 // Will be updated during execution
    });

    this.metrics.availableResources--;
  }

  private releaseResource(resourceId: string, requirements: ResourceRequirements): void {
    const resource = this.resources.get(resourceId);
    if (!resource) return;

    resource.allocated.value = Math.max(0, resource.allocated.value - requirements.cpu);
    resource.available.value = Math.min(resource.capacity.value, resource.available.value + requirements.cpu);
    resource.status = resource.available.value > 0 ? 'available' : 'allocated';

    // Update allocation history
    const lastAllocation = resource.allocationHistory[resource.allocationHistory.length - 1];
    if (lastAllocation && !lastAllocation.releasedAt) {
      lastAllocation.releasedAt = new Date();
      lastAllocation.duration = lastAllocation.releasedAt.getTime() - lastAllocation.allocatedAt.getTime();
    }

    this.metrics.availableResources++;
  }

  private shouldHandleOverflow(): boolean {
    return this.waitingQueue.length >= this.config.allocation.overflow.maxQueueSize;
  }

  private handleOverflow(taskId: string, requirements: ResourceRequirements, priority: number): Promise<ResourceAllocation> {
    const strategy = this.config.allocation.overflow.strategy;
    
    switch (strategy) {
      case 'reject':
        this.metrics.failedAllocations++;
        return Promise.reject(new Error(`Resource pool overflow: ${taskId}`));
      
      case 'degrade':
        // Attempt allocation with degraded requirements
        const degradedRequirements = this.degradeRequirements(requirements);
        return this.allocateResources(taskId, degradedRequirements, priority);
      
      default:
        this.metrics.failedAllocations++;
        return Promise.reject(new Error(`Resource pool overflow: ${taskId}`));
    }
  }

  private degradeRequirements(requirements: ResourceRequirements): ResourceRequirements {
    return {
      cpu: requirements.cpu * 0.7,
      memory: requirements.memory * 0.8,
      io: requirements.io * 0.9,
      network: requirements.network * 0.9
    };
  }

  private sortWaitingQueue(): void {
    this.waitingQueue.sort((a, b) => {
      // Higher priority first
      if (a.priority !== b.priority) {
        return b.priority - a.priority;
      }
      
      // Then by timestamp (FIFO)
      return a.timestamp.getTime() - b.timestamp.getTime();
    });
  }

  private processWaitingQueue(): void {
    const processed: string[] = [];
    
    for (let i = 0; i < this.waitingQueue.length; i++) {
      const request = this.waitingQueue[i];
      if (!request) continue;
      const allocation = this.tryAllocate(request.taskId, request.requirements, request.priority);
      
      if (allocation) {
        request.resolve(allocation);
        processed.push(request.taskId);
        this.metrics.successfulAllocations++;
      }
    }
    
    // Remove processed requests
    this.waitingQueue = this.waitingQueue.filter(req => !processed.includes(req.taskId));
  }

  private releaseAllAllocations(): void {
    for (const allocationId of this.allocations.keys()) {
      this.releaseResources(allocationId);
    }
  }

  private calculateAllocationUtilization(allocation: ResourceAllocation): number {
    // Simplified utilization calculation
    return Math.random() * 0.8 + 0.2; // Mock 20-100% utilization
  }

  private startMaintenance(): void {
    this.maintenanceTimer = setInterval(() => {
      this.performMaintenance();
    }, 60000); // Every minute
  }

  private startMonitoring(): void {
    this.monitoringTimer = setInterval(() => {
      this.updateMetrics();
      this.checkHealthStatus();
      this.checkAlerts();
    }, 10000); // Every 10 seconds
  }

  private performMaintenance(): void {
    // Cleanup expired allocations
    this.cleanupExpiredAllocations();
    
    // Perform defragmentation if needed
    if (this.shouldDefragment()) {
      this.defragment().catch(console.error);
    }
    
    // Scale pool if needed
    this.autoScale();
  }

  private cleanupExpiredAllocations(): void {
    const now = Date.now();
    const expired: string[] = [];
    
    for (const [id, allocation] of this.allocations) {
      if (allocation.expiresAt && now > allocation.expiresAt.getTime()) {
        expired.push(id);
      }
    }
    
    for (const id of expired) {
      this.releaseResources(id);
      this.emit('allocationExpired', { allocationId: id });
    }
  }

  private shouldDefragment(): boolean {
    if (!this.config.optimization.defragmentation.enabled) {
      return false;
    }
    
    return this.metrics.fragmentationRatio > this.config.optimization.defragmentation.threshold;
  }

  private async performDefragmentation(): Promise<void> {
    // Simplified defragmentation - compact available resources
    const availableResources = Array.from(this.resources.values())
      .filter(r => r.status === 'available');
    
    // Simulate defragmentation work
    await new Promise(resolve => setTimeout(resolve, 1000));
    
    console.log(`🧹 Defragmented ${availableResources.length} resources`);
  }

  private autoScale(): void {
    if (this.config.strategy !== 'dynamic' && this.config.strategy !== 'elastic') {
      return;
    }
    
    const utilization = this.metrics.utilizationRate;
    const currentSize = this.resources.size;
    
    if (utilization > this.config.sizing.scaleUpThreshold && 
        currentSize < this.config.sizing.maxSize) {
      this.scaleUp();
    } else if (utilization < this.config.sizing.scaleDownThreshold && 
               currentSize > this.config.sizing.minSize) {
      this.scaleDown();
    }
  }

  private scaleUp(): void {
    const increment = this.config.sizing.scaleUpIncrement;
    const currentSize = this.resources.size;
    const targetSize = Math.min(currentSize + increment, this.config.sizing.maxSize);
    
    for (let i = currentSize; i < targetSize; i++) {
      const resource = this.createResource(i);
      this.addResource(resource);
    }
    
    this.emit('poolScaledUp', { from: currentSize, to: targetSize });
  }

  private scaleDown(): void {
    const decrement = this.config.sizing.scaleDownDecrement;
    const currentSize = this.resources.size;
    const targetSize = Math.max(currentSize - decrement, this.config.sizing.minSize);
    
    // Remove least used available resources
    const availableResources = Array.from(this.resources.values())
      .filter(r => r.status === 'available')
      .sort((a, b) => a.lastUsed.getTime() - b.lastUsed.getTime());
    
    const toRemove = currentSize - targetSize;
    for (let i = 0; i < Math.min(toRemove, availableResources.length); i++) {
      this.removeResource(availableResources[i].id);
    }
    
    this.emit('poolScaledDown', { from: currentSize, to: this.resources.size });
  }

  private updateMetrics(): void {
    const totalResources = this.resources.size;
    const availableResources = Array.from(this.resources.values())
      .filter(r => r.status === 'available').length;
    const allocatedResources = totalResources - availableResources;
    
    this.metrics.totalResources = totalResources;
    this.metrics.availableResources = availableResources;
    this.metrics.allocatedResources = allocatedResources;
    this.metrics.utilizationRate = totalResources > 0 ? allocatedResources / totalResources : 0;
    this.metrics.allocationRate = this.metrics.successfulAllocations / 
      (this.metrics.successfulAllocations + this.metrics.failedAllocations + 1);
    this.metrics.fragmentationRatio = this.calculateFragmentationRatio();
  }

  private calculateFragmentationRatio(): number {
    // Simplified fragmentation calculation
    const totalCapacity = Array.from(this.resources.values())
      .reduce((sum, r) => sum + r.capacity.value, 0);
    const largestFreeBlock = Math.max(...Array.from(this.resources.values())
      .filter(r => r.status === 'available')
      .map(r => r.available.value), 0);
    
    return totalCapacity > 0 ? 1 - (largestFreeBlock / totalCapacity) : 0;
  }

  private checkHealthStatus(): void {
    if (!this.config.monitoring.healthChecking) {
      return;
    }
    
    for (const resource of this.resources.values()) {
      if (resource.metadata.healthCheck.enabled) {
        this.performHealthCheck(resource);
      }
    }
  }

  private performHealthCheck(resource: PooledResource): void {
    // Simulate health check
    const health = Math.random();
    const threshold = resource.metadata.healthCheck.healthThreshold;
    
    if (health < threshold) {
      resource.status = 'failed';
      this.emit('resourceHealthCheckFailed', { resource, health });
    }
  }

  private checkAlerts(): void {
    if (!this.config.monitoring.alerting.enabled) {
      return;
    }
    
    const thresholds = this.config.monitoring.alerting.thresholds;
    
    if (this.metrics.utilizationRate > thresholds.utilization) {
      this.emit('alert', {
        type: 'high_utilization',
        value: this.metrics.utilizationRate,
        threshold: thresholds.utilization
      });
    }
    
    if (this.metrics.availableResources / this.metrics.totalResources < thresholds.availability) {
      this.emit('alert', {
        type: 'low_availability',
        value: this.metrics.availableResources / this.metrics.totalResources,
        threshold: thresholds.availability
      });
    }
  }

  private applyConfigurationChanges(): void {
    // Apply sizing changes
    const currentSize = this.resources.size;
    const targetSize = this.config.sizing.initialSize;
    
    if (currentSize < targetSize) {
      this.scaleUp();
    } else if (currentSize > targetSize) {
      this.scaleDown();
    }
  }
}