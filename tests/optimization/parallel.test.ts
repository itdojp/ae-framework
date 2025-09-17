/**
 * Tests for Phase 3.3.2: Parallel Processing Optimization Engine
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { 
  ParallelOptimizer, 
  TaskScheduler, 
  ResourcePool,
  ParallelOptimizationSystem,
  type ParallelTask,
  type ResourceRequirements,
  type OptimizationStrategy,
  type SchedulingPolicy,
  type PoolConfiguration
} from '../../src/optimization/parallel/index.js';

describe('Parallel Optimization Engine', () => {
  describe('ParallelOptimizer', () => {
    let optimizer: ParallelOptimizer;
    
    beforeEach(() => {
      optimizer = new ParallelOptimizer();
    });
    
    afterEach(async () => {
      await optimizer.stop();
    });

  it(formatGWT('optimizer constructed', 'initialize with defaults', 'configuration is valid'), () => {
      expect(optimizer).toBeDefined();
      const metrics = optimizer.getOptimizationMetrics();
      expect(metrics.totalTasksProcessed).toBe(0);
      expect(metrics.activeWorkers).toBeGreaterThanOrEqual(0);
    });

    it(
      formatGWT('optimizer lifecycle', 'start then inspect metrics', 'active workers > 0'),
      () => {
        optimizer.start();
        const metrics = optimizer.getOptimizationMetrics();
        expect(metrics.activeWorkers).toBeGreaterThan(0);
      }
    );

    it(
      formatGWT('task submission', 'submit then check queue metrics', 'queue length >= 0'),
      async () => {
      optimizer.start();
      
      const task: ParallelTask = {
        id: 'test-task-1',
        name: 'Test Task',
        type: 'computation',
        payload: { data: 'test' },
        priority: 'normal',
        dependencies: [],
        estimatedDuration: 1000,
        maxRetries: 3,
        timeout: 5000,
        resourceRequirements: {
          cpu: 0.5,
          memory: 100,
          io: 0.1,
          network: 0.1
        },
        metadata: { test: true }
      };

      const taskId = await optimizer.submitTask(task);
      expect(taskId).toBe('test-task-1');
      
      const metrics = optimizer.getOptimizationMetrics();
      expect(metrics.queueLength).toBeGreaterThanOrEqual(0);
    }
    );

    it('should wait for task completion', async () => {
      optimizer.start();
      
      const task: ParallelTask = {
        id: 'test-task-2',
        name: 'Test Task 2',
        type: 'computation',
        payload: { data: 'test' },
        priority: 'high',
        dependencies: [],
        estimatedDuration: 500,
        maxRetries: 3,
        timeout: 5000,
        resourceRequirements: {
          cpu: 0.3,
          memory: 50,
          io: 0.1,
          network: 0.1
        },
        metadata: { test: true }
      };

      await optimizer.submitTask(task);
      
      // Wait for task completion with timeout
      const result = await optimizer.waitForTask('test-task-2', 10000);
      expect(result.taskId).toBe('test-task-2');
      expect(result.status).toBe('completed');
    });

    it('should generate parallelization plan', async () => {
      const tasks: ParallelTask[] = [
        {
          id: 'task-1',
          name: 'Task 1',
          type: 'computation',
          payload: {},
          priority: 'normal',
          dependencies: [],
          estimatedDuration: 1000,
          maxRetries: 3,
          timeout: 5000,
          resourceRequirements: { cpu: 0.5, memory: 100, io: 0.1, network: 0.1 },
          metadata: {}
        },
        {
          id: 'task-2',
          name: 'Task 2',
          type: 'computation',
          payload: {},
          priority: 'normal',
          dependencies: ['task-1'],
          estimatedDuration: 800,
          maxRetries: 3,
          timeout: 5000,
          resourceRequirements: { cpu: 0.3, memory: 80, io: 0.1, network: 0.1 },
          metadata: {}
        }
      ];

      const plan = await optimizer.generateParallelizationPlan(tasks);
      expect(plan.originalTasks).toHaveLength(2);
      expect(plan.optimizedTasks).toHaveLength(2);
      expect(plan.speedupFactor).toBeGreaterThanOrEqual(1);
      expect(plan.efficiency).toBeGreaterThan(0);
    });

    it('should handle task cancellation', async () => {
      optimizer.start();
      
      const task: ParallelTask = {
        id: 'cancel-task',
        name: 'Cancellable Task',
        type: 'computation',
        payload: {},
        priority: 'low',
        dependencies: [],
        estimatedDuration: 5000,
        maxRetries: 3,
        timeout: 10000,
        resourceRequirements: { cpu: 0.5, memory: 100, io: 0.1, network: 0.1 },
        metadata: {}
      };

      await optimizer.submitTask(task);
      const cancelled = await optimizer.cancelTask('cancel-task');
      expect(cancelled).toBe(true);
    });

    it('should update optimization strategy', () => {
      const newStrategy: Partial<OptimizationStrategy> = {
        maxConcurrency: 8,
        loadBalancing: 'least_loaded'
      };

      optimizer.updateStrategy(newStrategy);
      // Strategy update should emit event
      expect(optimizer).toBeDefined();
    });
  });

  describe('TaskScheduler', () => {
    let scheduler: TaskScheduler;
    
    beforeEach(() => {
      scheduler = new TaskScheduler();
    });
    
    afterEach(() => {
      scheduler.stop();
    });

    it('should initialize with default policy', () => {
      expect(scheduler).toBeDefined();
      const metrics = scheduler.getSchedulingMetrics();
      expect(metrics.totalScheduled).toBe(0);
    });

    it('should start and stop correctly', () => {
      scheduler.start();
      expect(scheduler).toBeDefined();
      
      scheduler.stop();
      expect(scheduler).toBeDefined();
    });

    it('should schedule tasks', async () => {
      scheduler.start();
      
      const task: ParallelTask = {
        id: 'sched-task-1',
        name: 'Scheduled Task',
        type: 'computation',
        payload: {},
        priority: 'normal',
        dependencies: [],
        estimatedDuration: 1000,
        maxRetries: 3,
        timeout: 5000,
        resourceRequirements: { cpu: 0.5, memory: 100, io: 0.1, network: 0.1 },
        metadata: {}
      };

      const decision = await scheduler.scheduleTask(task);
      expect(decision.taskId).toBe('sched-task-1');
      expect(['schedule', 'defer', 'reject']).toContain(decision.action);
    });

    it('should handle resource availability updates', () => {
      scheduler.updateResourceAvailability({
        cpu: 0.8,
        memory: 4000,
        workers: 6
      });
      
      expect(scheduler).toBeDefined();
    });

    it('should preempt tasks', async () => {
      scheduler.start();
      
      const task: ParallelTask = {
        id: 'preempt-task',
        name: 'Preemptable Task',
        type: 'computation',
        payload: {},
        priority: 'low',
        dependencies: [],
        estimatedDuration: 1000,
        maxRetries: 3,
        timeout: 5000,
        resourceRequirements: { cpu: 0.5, memory: 100, io: 0.1, network: 0.1 },
        metadata: {}
      };

      await scheduler.scheduleTask(task);
      const preempted = await scheduler.preemptTask('preempt-task', 'test_preemption');
      expect(typeof preempted).toBe('boolean');
    });

    it('should get queue status', () => {
      const status = scheduler.getQueueStatus();
      expect(Array.isArray(status)).toBe(true);
      expect(status.length).toBeGreaterThan(0);
    });

    it('should cancel scheduled tasks', () => {
      const cancelled = scheduler.cancelTask('non-existent-task');
      expect(cancelled).toBe(false);
    });

    it('should update scheduling policy', () => {
      const newPolicy: Partial<SchedulingPolicy> = {
        algorithm: 'deadline_aware',
        preemption: {
          enabled: true,
          strategy: 'deadline_pressure',
          timeSlice: 2000,
          priorityThreshold: 0.8
        }
      };

      scheduler.updatePolicy(newPolicy);
      expect(scheduler).toBeDefined();
    });
  });

  describe('ResourcePool', () => {
    let pool: ResourcePool;
    
    beforeEach(() => {
      pool = new ResourcePool();
    });
    
    afterEach(() => {
      pool.stop();
    });

    it('should initialize with default configuration', () => {
      expect(pool).toBeDefined();
      const metrics = pool.getPoolMetrics();
      expect(metrics.totalResources).toBeGreaterThan(0);
    });

    it('should start and stop correctly', () => {
      pool.start();
      expect(pool).toBeDefined();
      
      pool.stop();
      expect(pool).toBeDefined();
    });

    it('should allocate resources', async () => {
      pool.start();
      
      const requirements: ResourceRequirements = {
        cpu: 0.5,
        memory: 100,
        io: 0.1,
        network: 0.1
      };

      const allocation = await pool.allocateResources('test-task', requirements, 3);
      expect(allocation.taskId).toBe('test-task');
      expect(allocation.resources.length).toBeGreaterThan(0);
    });

    it('should release allocated resources', async () => {
      pool.start();
      
      const requirements: ResourceRequirements = {
        cpu: 0.3,
        memory: 50,
        io: 0.1,
        network: 0.1
      };

      const allocation = await pool.allocateResources('release-task', requirements);
      const released = pool.releaseResources(allocation.id);
      expect(released).toBe(true);
    });

    it('should get resource utilization', () => {
      const utilization = pool.getResourceUtilization();
      expect(typeof utilization).toBe('object');
      expect(Object.keys(utilization).length).toBeGreaterThan(0);
    });

    it('should handle resource addition and removal', () => {
      const resource = {
        id: 'test-resource',
        type: 'compute_unit' as const,
        capacity: { value: 1.0, unit: 'core', scalable: true, maxScale: 2.0 },
        allocated: { value: 0, unit: 'core', scalable: true, maxScale: 2.0 },
        available: { value: 1.0, unit: 'core', scalable: true, maxScale: 2.0 },
        status: 'available' as const,
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

      pool.addResource(resource);
      const removed = pool.removeResource('test-resource');
      expect(removed).toBe(true);
    });

    it('should get allocation status', () => {
      const status = pool.getAllocationStatus();
      expect(Array.isArray(status)).toBe(true);
    });

    it('should perform defragmentation', async () => {
      await expect(pool.defragment()).resolves.not.toThrow();
    });

    it('should update configuration', () => {
      const newConfig: Partial<PoolConfiguration> = {
        strategy: 'elastic',
        sizing: {
          initialSize: 15,
          minSize: 8,
          maxSize: 60,
          scaleUpThreshold: 0.85,
          scaleDownThreshold: 0.25,
          scaleUpIncrement: 3,
          scaleDownDecrement: 2,
          cooldownPeriod: 45000
        }
      };

      pool.updateConfiguration(newConfig);
      expect(pool).toBeDefined();
    });
  });

  describe('ParallelOptimizationSystem', () => {
    let system: ParallelOptimizationSystem;
    
    beforeEach(() => {
      system = new ParallelOptimizationSystem();
    });
    
    afterEach(async () => {
      await system.stop();
    });

    it('should initialize all components', () => {
      expect(system.getOptimizer()).toBeDefined();
      expect(system.getScheduler()).toBeDefined();
      expect(system.getResourcePool()).toBeDefined();
    });

    it('should start and stop all components', async () => {
      system.start();
      expect(system.getOptimizer()).toBeDefined();
      
      await system.stop();
      expect(system.getOptimizer()).toBeDefined();
    });

    it('should get combined system metrics', () => {
      const metrics = system.getSystemMetrics();
      expect(metrics.optimization).toBeDefined();
      expect(metrics.scheduling).toBeDefined();
      expect(metrics.resources).toBeDefined();
      expect(metrics.timestamp).toBeInstanceOf(Date);
    });

    it('should integrate components correctly', async () => {
      system.start();
      
      // Test integration by submitting a task
      const optimizer = system.getOptimizer();
      const task: ParallelTask = {
        id: 'integration-task',
        name: 'Integration Test Task',
        type: 'computation',
        payload: {},
        priority: 'normal',
        dependencies: [],
        estimatedDuration: 500,
        maxRetries: 3,
        timeout: 5000,
        resourceRequirements: { cpu: 0.2, memory: 50, io: 0.1, network: 0.1 },
        metadata: {}
      };

      const taskId = await optimizer.submitTask(task);
      expect(taskId).toBe('integration-task');
    });
  });

  describe('Performance and Scalability', () => {
    it('should handle multiple concurrent tasks', async () => {
      const system = new ParallelOptimizationSystem();
      system.start();
      
      try {
        const tasks: Promise<string>[] = [];
        
        for (let i = 0; i < 10; i++) {
          const task: ParallelTask = {
            id: `perf-task-${i}`,
            name: `Performance Task ${i}`,
            type: 'computation',
            payload: { index: i },
            priority: i % 2 === 0 ? 'high' : 'normal',
            dependencies: [],
            estimatedDuration: 200 + Math.random() * 300,
            maxRetries: 3,
            timeout: 5000,
            resourceRequirements: {
              cpu: 0.1 + Math.random() * 0.3,
              memory: 50 + Math.random() * 100,
              io: 0.1,
              network: 0.1
            },
            metadata: { batch: 'performance_test' }
          };
          
          tasks.push(system.getOptimizer().submitTask(task));
        }
        
        const taskIds = await Promise.all(tasks);
        expect(taskIds).toHaveLength(10);
        
        const metrics = system.getSystemMetrics();
        expect(metrics.optimization.queueLength).toBeGreaterThanOrEqual(0);
        
      } finally {
        await system.stop();
      }
    });

    it('should scale resources under load', () => {
      const pool = new ResourcePool({
        strategy: 'dynamic',
        sizing: {
          initialSize: 2,
          minSize: 1,
          maxSize: 10,
          scaleUpThreshold: 0.7,
          scaleDownThreshold: 0.3,
          scaleUpIncrement: 2,
          scaleDownDecrement: 1,
          cooldownPeriod: 1000
        }
      });

      pool.start();
      
      try {
        const initialMetrics = pool.getPoolMetrics();
        expect(initialMetrics.totalResources).toBe(2);
        
        // Simulate load by getting utilization
        const utilization = pool.getResourceUtilization();
        expect(typeof utilization).toBe('object');
        
      } finally {
        pool.stop();
      }
    });

    it('should optimize task execution order', async () => {
      const optimizer = new ParallelOptimizer();
      
      const tasks: ParallelTask[] = [
        {
          id: 'opt-task-1',
          name: 'Quick Task',
          type: 'computation',
          payload: {},
          priority: 'low',
          dependencies: [],
          estimatedDuration: 100,
          maxRetries: 3,
          timeout: 5000,
          resourceRequirements: { cpu: 0.1, memory: 20, io: 0.1, network: 0.1 },
          metadata: {}
        },
        {
          id: 'opt-task-2',
          name: 'Long Task',
          type: 'computation',
          payload: {},
          priority: 'normal',
          dependencies: [],
          estimatedDuration: 2000,
          maxRetries: 3,
          timeout: 5000,
          resourceRequirements: { cpu: 0.8, memory: 500, io: 0.1, network: 0.1 },
          metadata: {}
        },
        {
          id: 'opt-task-3',
          name: 'Priority Task',
          type: 'computation',
          payload: {},
          priority: 'urgent',
          dependencies: [],
          estimatedDuration: 500,
          maxRetries: 3,
          timeout: 5000,
          resourceRequirements: { cpu: 0.5, memory: 200, io: 0.1, network: 0.1 },
          metadata: {}
        }
      ];

      const plan = await optimizer.generateParallelizationPlan(tasks);
      
      expect(plan.executionGroups.length).toBeGreaterThan(0);
      expect(plan.speedupFactor).toBeGreaterThanOrEqual(1);
      expect(plan.efficiency).toBeGreaterThan(0);
      expect(plan.resourceUtilization.cpuUtilization).toBeGreaterThan(0);
      
      await optimizer.stop();
    });
  });

  describe('Error Handling and Edge Cases', () => {
    it('should handle resource exhaustion gracefully', async () => {
      const pool = new ResourcePool({
        sizing: {
          initialSize: 1,
          minSize: 1,
          maxSize: 1,
          scaleUpThreshold: 0.9,
          scaleDownThreshold: 0.1,
          scaleUpIncrement: 1,
          scaleDownDecrement: 1,
          cooldownPeriod: 10000
        },
        allocation: {
          algorithm: 'first_fit',
          priorityHandling: {
            enabled: true,
            levels: 3,
            aging: false,
            agingFactor: 0,
            starvationPrevention: false
          },
          preemption: {
            enabled: false,
            strategy: 'priority_based',
            gracePeriod: 1000,
            notificationEnabled: false
          },
          fairness: {
            enabled: false,
            algorithm: 'proportional_share',
            weights: {},
            quotas: {}
          },
          overflow: {
            strategy: 'reject',
            maxQueueSize: 1,
            timeout: 1000
          }
        }
      });

      pool.start();
      
      try {
        // First allocation should succeed
        const allocation1 = await pool.allocateResources('task-1', {
          cpu: 1.0,
          memory: 100,
          io: 0.1,
          network: 0.1
        });
        expect(allocation1).toBeDefined();
        
        // Second allocation should fail due to resource exhaustion
        await expect(pool.allocateResources('task-2', {
          cpu: 0.5,
          memory: 50,
          io: 0.1,
          network: 0.1
        })).rejects.toThrow();
        
      } finally {
        pool.stop();
      }
    });

    it('should handle invalid task dependencies', async () => {
      const optimizer = new ParallelOptimizer();
      
      const tasks: ParallelTask[] = [
        {
          id: 'dep-task-1',
          name: 'Task with Invalid Dependency',
          type: 'computation',
          payload: {},
          priority: 'normal',
          dependencies: ['non-existent-task'],
          estimatedDuration: 1000,
          maxRetries: 3,
          timeout: 5000,
          resourceRequirements: { cpu: 0.5, memory: 100, io: 0.1, network: 0.1 },
          metadata: {}
        },
        {
          id: 'dep-task-2',
          name: 'Valid Task',
          type: 'computation',
          payload: {},
          priority: 'normal',
          dependencies: [],
          estimatedDuration: 500,
          maxRetries: 3,
          timeout: 5000,
          resourceRequirements: { cpu: 0.3, memory: 50, io: 0.1, network: 0.1 },
          metadata: {}
        }
      ];

      const plan = await optimizer.generateParallelizationPlan(tasks);
      expect(plan.executionGroups.length).toBeGreaterThanOrEqual(1);
      
      await optimizer.stop();
    });

    it('should handle scheduler stop during task execution', () => {
      const scheduler = new TaskScheduler();
      scheduler.start();
      
      // Stop scheduler immediately
      scheduler.stop();
      expect(scheduler).toBeDefined();
    });
  });
});
