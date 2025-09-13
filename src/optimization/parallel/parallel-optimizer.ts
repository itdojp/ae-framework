/**
 * Parallel Optimizer for Phase 3.3.2
 * Intelligent parallel processing optimization and task distribution
 */

import { EventEmitter } from 'events';
import type { Worker } from 'worker_threads';
import { cpus } from 'os';

export interface ParallelTask<T = any, R = any> {
  id: string;
  name: string;
  type: TaskType;
  payload: T;
  priority: TaskPriority;
  dependencies: string[];
  estimatedDuration: number;
  maxRetries: number;
  timeout: number;
  resourceRequirements: ResourceRequirements;
  metadata: Record<string, any>;
}

export type TaskType = 
  | 'cpu_intensive'
  | 'io_bound'
  | 'memory_intensive'
  | 'network_request'
  | 'computation'
  | 'analysis'
  | 'test_execution'
  | 'code_generation';

export type TaskPriority = 'urgent' | 'high' | 'normal' | 'low' | 'background';

export interface ResourceRequirements {
  cpu: number;        // CPU cores required (0-1 scale)
  memory: number;     // Memory in MB
  io: number;         // IO bandwidth requirement (0-1 scale)
  network: number;    // Network bandwidth requirement (0-1 scale)
}

export interface TaskResult<R = any> {
  taskId: string;
  status: 'completed' | 'failed' | 'timeout' | 'cancelled';
  result?: R;
  error?: string;
  executionTime: number;
  resourceUsage: ResourceUsage;
  workerId?: string;
  retryCount: number;
}

export interface ResourceUsage {
  cpuTime: number;
  memoryPeak: number;
  ioOperations: number;
  networkBytes: number;
}

export interface OptimizationStrategy {
  name: string;
  description: string;
  maxConcurrency: number;
  loadBalancing: LoadBalancingStrategy;
  priorityWeighting: PriorityWeights;
  resourceAllocation: ResourceAllocationStrategy;
  adaptiveScaling: AdaptiveScalingConfig;
}

export type LoadBalancingStrategy = 
  | 'round_robin'
  | 'least_loaded'
  | 'resource_aware'
  | 'task_affinity'
  | 'smart_dispatch';

export interface PriorityWeights {
  urgent: number;
  high: number;
  normal: number;
  low: number;
  background: number;
}

export type ResourceAllocationStrategy = 
  | 'static'
  | 'dynamic'
  | 'predictive'
  | 'fair_share'
  | 'greedy';

export interface AdaptiveScalingConfig {
  enabled: boolean;
  scaleUpThreshold: number;
  scaleDownThreshold: number;
  maxWorkers: number;
  minWorkers: number;
  cooldownPeriod: number;
}

export interface ParallelizationPlan {
  id: string;
  originalTasks: ParallelTask[];
  optimizedTasks: OptimizedTask[];
  executionGroups: TaskGroup[];
  estimatedParallelTime: number;
  estimatedSequentialTime: number;
  speedupFactor: number;
  efficiency: number;
  resourceUtilization: ResourceUtilizationPlan;
}

export interface OptimizedTask extends ParallelTask {
  groupId: string;
  executionOrder: number;
  assignedResources: ResourceRequirements;
  scheduledStartTime: number;
  dependencies: string[];
}

export interface TaskGroup {
  id: string;
  tasks: string[];
  parallelExecutable: boolean;
  estimatedDuration: number;
  resourceRequirements: ResourceRequirements;
  dependencies: string[];
}

export interface ResourceUtilizationPlan {
  cpuUtilization: number;
  memoryUtilization: number;
  ioUtilization: number;
  networkUtilization: number;
  efficiency: number;
  bottlenecks: string[];
}

export interface OptimizationMetrics {
  totalTasksProcessed: number;
  averageExecutionTime: number;
  parallelEfficiency: number;
  resourceUtilization: number;
  successRate: number;
  throughput: number;
  queueLength: number;
  activeWorkers: number;
}

export class ParallelOptimizer extends EventEmitter {
  private strategy: OptimizationStrategy;
  private activeWorkers = new Map<string, Worker>();
  private taskQueue: ParallelTask[] = [];
  private executingTasks = new Map<string, ParallelTask>();
  private completedTasks = new Map<string, TaskResult>();
  private resourceUsage: ResourceUsage = {
    cpuTime: 0,
    memoryPeak: 0,
    ioOperations: 0,
    networkBytes: 0
  };
  private metrics: OptimizationMetrics = {
    totalTasksProcessed: 0,
    averageExecutionTime: 0,
    parallelEfficiency: 0,
    resourceUtilization: 0,
    successRate: 0,
    throughput: 0,
    queueLength: 0,
    activeWorkers: 0
  };
  private isRunning = false;
  private optimizationTimer?: NodeJS.Timeout;

  constructor(strategy?: Partial<OptimizationStrategy>) {
    super();
    this.strategy = this.createDefaultStrategy(strategy);
    this.setupWorkerPool();
  }

  /**
   * Start the parallel optimizer
   */
  start(): void {
    if (this.isRunning) {
      return;
    }

    this.isRunning = true;
    this.startOptimizationLoop();
    this.emit('optimizerStarted');
    
    console.log(`🚀 Parallel Optimizer started with ${this.strategy.maxConcurrency} workers`);
  }

  /**
   * Stop the parallel optimizer
   */
  async stop(): Promise<void> {
    if (!this.isRunning) {
      return;
    }

    this.isRunning = false;
    
    // Stop optimization loop
    if (this.optimizationTimer) {
      clearInterval(this.optimizationTimer);
      delete this.optimizationTimer;
    }

    // Terminate all workers
    await this.terminateAllWorkers();
    
    this.emit('optimizerStopped');
    console.log('🛑 Parallel Optimizer stopped');
  }

  /**
   * Submit a task for parallel execution
   */
  async submitTask<T, R>(task: ParallelTask<T, R>): Promise<string> {
    if (!this.isRunning) {
      throw new Error('Parallel Optimizer is not running');
    }

    this.taskQueue.push(task);
    this.sortTasksByPriority();
    this.metrics.queueLength = this.taskQueue.length;
    
    this.emit('taskSubmitted', task);
    
    // Trigger immediate processing
    this.processTaskQueue();
    
    return task.id;
  }

  /**
   * Get task result
   */
  getTaskResult<R>(taskId: string): TaskResult<R> | null {
    return this.completedTasks.get(taskId) as TaskResult<R> || null;
  }

  /**
   * Wait for task completion
   */
  async waitForTask<R>(taskId: string, timeout = 30000): Promise<TaskResult<R>> {
    return new Promise((resolve, reject) => {
      const checkResult = () => {
        const result = this.getTaskResult<R>(taskId);
        if (result) {
          resolve(result);
          return;
        }
        
        setTimeout(checkResult, 100);
      };

      // Start checking
      checkResult();

      // Set timeout
      setTimeout(() => {
        reject(new Error(`Task ${taskId} timed out after ${timeout}ms`));
      }, timeout);
    });
  }

  /**
   * Generate parallelization plan for a set of tasks
   */
  async generateParallelizationPlan(tasks: ParallelTask[]): Promise<ParallelizationPlan> {
    // Analyze task dependencies
    const dependencyGraph = this.buildDependencyGraph(tasks);
    
    // Group tasks that can run in parallel
    const taskGroups = this.groupTasksForParallelExecution(tasks, dependencyGraph);
    
    // Optimize task scheduling
    const optimizedTasks = this.optimizeTaskScheduling(tasks, taskGroups);
    
    // Calculate time estimates
    const sequentialTime = tasks.reduce((sum, task) => sum + task.estimatedDuration, 0);
    const parallelTime = this.calculateParallelExecutionTime(taskGroups);
    
    // Calculate efficiency metrics
    const speedupFactor = sequentialTime / parallelTime;
    const efficiency = speedupFactor / this.strategy.maxConcurrency;
    
    // Plan resource utilization
    const resourceUtilization = this.planResourceUtilization(optimizedTasks);
    
    return {
      id: `plan-${Date.now()}`,
      originalTasks: tasks,
      optimizedTasks,
      executionGroups: taskGroups,
      estimatedParallelTime: parallelTime,
      estimatedSequentialTime: sequentialTime,
      speedupFactor,
      efficiency,
      resourceUtilization
    };
  }

  /**
   * Execute tasks based on parallelization plan
   */
  async executeParallelizationPlan<R>(plan: ParallelizationPlan): Promise<TaskResult<R>[]> {
    const results: TaskResult<R>[] = [];
    
    this.emit('planExecutionStarted', plan);
    
    try {
      // Execute task groups in dependency order
      for (const group of plan.executionGroups) {
        if (group.parallelExecutable) {
          // Execute tasks in parallel
          const groupResults = await this.executeTaskGroupParallel<R>(group, plan);
          results.push(...groupResults);
        } else {
          // Execute tasks sequentially
          const groupResults = await this.executeTaskGroupSequential<R>(group, plan);
          results.push(...groupResults);
        }
      }
      
      this.emit('planExecutionCompleted', { plan, results });
      
    } catch (error) {
      this.emit('planExecutionError', { plan, error });
      throw error;
    }
    
    return results;
  }

  /**
   * Get current optimization metrics
   */
  getOptimizationMetrics(): OptimizationMetrics {
    this.updateMetrics();
    return { ...this.metrics };
  }

  /**
   * Update optimization strategy
   */
  updateStrategy(updates: Partial<OptimizationStrategy>): void {
    this.strategy = { ...this.strategy, ...updates };
    this.emit('strategyUpdated', this.strategy);
    
    // Apply new strategy
    this.applyNewStrategy();
  }

  /**
   * Get current resource usage
   */
  getCurrentResourceUsage(): ResourceUsage {
    return { ...this.resourceUsage };
  }

  /**
   * Cancel a task
   */
  async cancelTask(taskId: string): Promise<boolean> {
    // Remove from queue
    const queueIndex = this.taskQueue.findIndex(task => task.id === taskId);
    if (queueIndex !== -1) {
      this.taskQueue.splice(queueIndex, 1);
      this.emit('taskCancelled', { taskId, reason: 'cancelled_from_queue' });
      return true;
    }

    // Cancel executing task
    const executingTask = this.executingTasks.get(taskId);
    if (executingTask) {
      // Find and terminate the worker
      for (const [workerId, worker] of this.activeWorkers) {
        // In a real implementation, we'd track which worker is executing which task
        // For now, we'll simulate cancellation
        break;
      }
      
      this.executingTasks.delete(taskId);
      this.completedTasks.set(taskId, {
        taskId,
        status: 'cancelled',
        executionTime: 0,
        resourceUsage: {
          cpuTime: 0,
          memoryPeak: 0,
          ioOperations: 0,
          networkBytes: 0
        },
        retryCount: 0
      });
      
      this.emit('taskCancelled', { taskId, reason: 'cancelled_during_execution' });
      return true;
    }

    return false;
  }

  // Private methods
  private createDefaultStrategy(overrides?: Partial<OptimizationStrategy>): OptimizationStrategy {
    const defaultConcurrency = Math.max(1, Math.min(cpus().length, 8));
    
    return {
      name: 'Intelligent Parallel Optimization',
      description: 'Adaptive parallel processing with smart resource allocation',
      maxConcurrency: defaultConcurrency,
      loadBalancing: 'resource_aware',
      priorityWeighting: {
        urgent: 1.0,
        high: 0.8,
        normal: 0.6,
        low: 0.4,
        background: 0.2
      },
      resourceAllocation: 'dynamic',
      adaptiveScaling: {
        enabled: true,
        scaleUpThreshold: 0.8,
        scaleDownThreshold: 0.3,
        maxWorkers: defaultConcurrency * 2,
        minWorkers: 1,
        cooldownPeriod: 30000
      },
      ...overrides
    };
  }

  private setupWorkerPool(): void {
    // Initialize minimum workers
    for (let i = 0; i < this.strategy.adaptiveScaling.minWorkers; i++) {
      this.createWorker();
    }
  }

  private createWorker(): string {
    const workerId = `worker-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;
    
    // Demo implementation: simulates worker behavior with mock object
    // TODO: In production, replace with actual Worker threads or process pools
    // Example: new Worker(workerScript, { workerData: config })
    const mockWorker = {
      postMessage: (message: any) => {
        // Demo simulation: uses setTimeout to mimic async worker execution
        // TODO: Replace with actual worker communication protocol
        setTimeout(() => {
          this.handleWorkerMessage(workerId, {
            type: 'task_completed',
            taskId: message.taskId,
            result: { success: true },
            executionTime: Math.random() * 1000 + 100
          });
        }, Math.random() * 1000 + 100);
      },
      terminate: () => {
        console.log(`🔧 Worker ${workerId} terminated`);
      }
    } as any;

    this.activeWorkers.set(workerId, mockWorker);
    this.metrics.activeWorkers = this.activeWorkers.size;
    
    console.log(`🔧 Created worker: ${workerId}`);
    return workerId;
  }

  private async terminateAllWorkers(): Promise<void> {
    const terminationPromises = Array.from(this.activeWorkers.entries()).map(
      async ([workerId, worker]) => {
        try {
          await worker.terminate();
        } catch (error) {
          console.warn(`Warning: Error terminating worker ${workerId}:`, error);
        }
      }
    );

    await Promise.all(terminationPromises);
    this.activeWorkers.clear();
    this.metrics.activeWorkers = 0;
  }

  private startOptimizationLoop(): void {
    this.optimizationTimer = setInterval(() => {
      this.processTaskQueue();
      this.updateMetrics();
      this.adaptiveScaling();
    }, 1000); // Run every second
  }

  private processTaskQueue(): void {
    if (this.taskQueue.length === 0) {
      return;
    }

    const availableWorkers = this.getAvailableWorkers();
    if (availableWorkers.length === 0) {
      return;
    }

    // Process tasks based on load balancing strategy
    const tasksToProcess = this.selectTasksForProcessing(availableWorkers.length);
    
    for (let i = 0; i < Math.min(tasksToProcess.length, availableWorkers.length); i++) {
      const task = tasksToProcess[i];
      const workerId = availableWorkers[i];
      
      if (task && workerId) {
        this.executeTask(task, workerId);
      }
    }
  }

  private selectTasksForProcessing(maxTasks: number): ParallelTask[] {
    // Sort by priority and select eligible tasks
    this.sortTasksByPriority();
    
    const eligible: ParallelTask[] = [];
    
    for (const task of this.taskQueue) {
      // Check if task dependencies are satisfied
      if (this.areTaskDependenciesSatisfied(task)) {
        eligible.push(task);
        if (eligible.length >= maxTasks) {
          break;
        }
      }
    }
    
    return eligible;
  }

  private areTaskDependenciesSatisfied(task: ParallelTask): boolean {
    return task.dependencies.every(depId => 
      this.completedTasks.has(depId) && 
      this.completedTasks.get(depId)?.status === 'completed'
    );
  }

  private executeTask(task: ParallelTask, workerId: string): void {
    // Remove from queue
    const queueIndex = this.taskQueue.findIndex(t => t.id === task.id);
    if (queueIndex !== -1) {
      this.taskQueue.splice(queueIndex, 1);
    }
    
    // Add to executing tasks
    this.executingTasks.set(task.id, task);
    
    // Send to worker
    const worker = this.activeWorkers.get(workerId);
    if (worker) {
      worker.postMessage({
        type: 'execute_task',
        taskId: task.id,
        task: task
      });
      
      this.emit('taskStarted', { task, workerId });
    }
  }

  private handleWorkerMessage(workerId: string, message: any): void {
    switch (message.type) {
      case 'task_completed':
        this.handleTaskCompleted(workerId, message);
        break;
      case 'task_error':
        this.handleTaskError(workerId, message);
        break;
      case 'resource_usage':
        this.updateResourceUsage(message.usage);
        break;
    }
  }

  private handleTaskCompleted(workerId: string, message: any): void {
    const task = this.executingTasks.get(message.taskId);
    if (!task) {
      return;
    }

    const result: TaskResult = {
      taskId: message.taskId,
      status: 'completed',
      result: message.result,
      executionTime: message.executionTime,
      resourceUsage: message.resourceUsage || {
        cpuTime: message.executionTime,
        memoryPeak: 0,
        ioOperations: 0,
        networkBytes: 0
      },
      workerId,
      retryCount: 0
    };

    this.executingTasks.delete(message.taskId);
    this.completedTasks.set(message.taskId, result);
    
    this.emit('taskCompleted', { task, result });
  }

  private handleTaskError(workerId: string, message: any): void {
    const task = this.executingTasks.get(message.taskId);
    if (!task) {
      return;
    }

    const result: TaskResult = {
      taskId: message.taskId,
      status: 'failed',
      error: message.error,
      executionTime: message.executionTime || 0,
      resourceUsage: {
        cpuTime: 0,
        memoryPeak: 0,
        ioOperations: 0,
        networkBytes: 0
      },
      workerId,
      retryCount: 0
    };

    this.executingTasks.delete(message.taskId);
    
    // Check if task should be retried
    if (task.maxRetries > 0) {
      task.maxRetries--;
      this.taskQueue.unshift(task); // Add to front of queue for retry
      this.emit('taskRetry', { task, error: message.error });
    } else {
      this.completedTasks.set(message.taskId, result);
      this.emit('taskFailed', { task, result });
    }
  }

  private updateResourceUsage(usage: Partial<ResourceUsage>): void {
    if (usage.cpuTime) this.resourceUsage.cpuTime += usage.cpuTime;
    if (usage.memoryPeak) this.resourceUsage.memoryPeak = Math.max(this.resourceUsage.memoryPeak, usage.memoryPeak);
    if (usage.ioOperations) this.resourceUsage.ioOperations += usage.ioOperations;
    if (usage.networkBytes) this.resourceUsage.networkBytes += usage.networkBytes;
  }

  private sortTasksByPriority(): void {
    const priorityValues = this.strategy.priorityWeighting;
    
    this.taskQueue.sort((a, b) => {
      const aPriority = priorityValues[a.priority];
      const bPriority = priorityValues[b.priority];
      
      if (aPriority !== bPriority) {
        return bPriority - aPriority; // Higher priority first
      }
      
      // Secondary sort by estimated duration (shorter first)
      return a.estimatedDuration - b.estimatedDuration;
    });
  }

  private getAvailableWorkers(): string[] {
    // For this simulation, all workers are always available
    // In a real implementation, we'd track worker states
    return Array.from(this.activeWorkers.keys());
  }

  private updateMetrics(): void {
    const completed = this.completedTasks.size;
    const successful = Array.from(this.completedTasks.values())
      .filter(r => r.status === 'completed').length;
    
    this.metrics.totalTasksProcessed = completed;
    this.metrics.successRate = completed > 0 ? successful / completed : 0;
    this.metrics.queueLength = this.taskQueue.length;
    this.metrics.activeWorkers = this.activeWorkers.size;
    
    // Calculate average execution time
    const executionTimes = Array.from(this.completedTasks.values())
      .map(r => r.executionTime);
    this.metrics.averageExecutionTime = executionTimes.length > 0 
      ? executionTimes.reduce((sum, time) => sum + time, 0) / executionTimes.length 
      : 0;
    
    // Calculate parallel efficiency
    this.metrics.parallelEfficiency = this.calculateParallelEfficiency();
    
    // Calculate resource utilization
    this.metrics.resourceUtilization = this.calculateResourceUtilization();
    
    // Calculate throughput (tasks per second)
    this.metrics.throughput = this.calculateThroughput();
  }

  private calculateParallelEfficiency(): number {
    const activeWorkerCount = this.activeWorkers.size;
    const executingTaskCount = this.executingTasks.size;
    
    return activeWorkerCount > 0 ? executingTaskCount / activeWorkerCount : 0;
  }

  private calculateResourceUtilization(): number {
    // Simplified resource utilization calculation
    const maxCpu = this.strategy.maxConcurrency;
    const currentCpu = this.executingTasks.size;
    
    return maxCpu > 0 ? currentCpu / maxCpu : 0;
  }

  private calculateThroughput(): number {
    // Tasks completed in the last minute
    const oneMinuteAgo = Date.now() - 60000;
    const recentCompletions = Array.from(this.completedTasks.values())
      .filter(r => (Date.now() - r.executionTime) < 60000);
    
    return recentCompletions.length / 60; // Per second
  }

  private adaptiveScaling(): void {
    if (!this.strategy.adaptiveScaling.enabled) {
      return;
    }

    const utilization = this.metrics.resourceUtilization;
    const currentWorkers = this.activeWorkers.size;
    const { scaleUpThreshold, scaleDownThreshold, maxWorkers, minWorkers } = this.strategy.adaptiveScaling;

    // Scale up if utilization is high
    if (utilization > scaleUpThreshold && currentWorkers < maxWorkers) {
      this.createWorker();
      this.emit('scaledUp', { newWorkerCount: this.activeWorkers.size });
    }
    
    // Scale down if utilization is low
    else if (utilization < scaleDownThreshold && currentWorkers > minWorkers) {
      const workersToRemove = Array.from(this.activeWorkers.keys()).slice(-1);
      for (const workerId of workersToRemove) {
        const worker = this.activeWorkers.get(workerId);
        if (worker) {
          worker.terminate();
          this.activeWorkers.delete(workerId);
        }
      }
      this.metrics.activeWorkers = this.activeWorkers.size;
      this.emit('scaledDown', { newWorkerCount: this.activeWorkers.size });
    }
  }

  private applyNewStrategy(): void {
    // Apply new concurrency limits
    const currentWorkers = this.activeWorkers.size;
    const targetWorkers = this.strategy.maxConcurrency;

    if (currentWorkers < targetWorkers) {
      // Add workers
      for (let i = currentWorkers; i < targetWorkers; i++) {
        this.createWorker();
      }
    } else if (currentWorkers > targetWorkers) {
      // Remove excess workers
      const workersToRemove = Array.from(this.activeWorkers.keys()).slice(targetWorkers);
      for (const workerId of workersToRemove) {
        const worker = this.activeWorkers.get(workerId);
        if (worker) {
          worker.terminate();
          this.activeWorkers.delete(workerId);
        }
      }
    }

    this.metrics.activeWorkers = this.activeWorkers.size;
  }

  // Parallelization planning methods
  private buildDependencyGraph(tasks: ParallelTask[]): Map<string, string[]> {
    const graph = new Map<string, string[]>();
    
    for (const task of tasks) {
      graph.set(task.id, task.dependencies);
    }
    
    return graph;
  }

  private groupTasksForParallelExecution(
    tasks: ParallelTask[], 
    dependencyGraph: Map<string, string[]>
  ): TaskGroup[] {
    const groups: TaskGroup[] = [];
    const processed = new Set<string>();
    
    // Topological sort to determine execution order
    const sortedTasks = this.topologicalSort(tasks, dependencyGraph);
    
    let currentGroup: TaskGroup = {
      id: `group-0`,
      tasks: [],
      parallelExecutable: true,
      estimatedDuration: 0,
      resourceRequirements: { cpu: 0, memory: 0, io: 0, network: 0 },
      dependencies: []
    };
    
    for (const task of sortedTasks) {
      // Check if task can be added to current group
      if (this.canAddToGroup(task, currentGroup, processed)) {
        currentGroup.tasks.push(task.id);
        currentGroup.estimatedDuration = Math.max(currentGroup.estimatedDuration, task.estimatedDuration);
        this.updateGroupResourceRequirements(currentGroup, task.resourceRequirements);
      } else {
        // Start new group
        if (currentGroup.tasks.length > 0) {
          groups.push(currentGroup);
        }
        
        currentGroup = {
          id: `group-${groups.length}`,
          tasks: [task.id],
          parallelExecutable: true,
          estimatedDuration: task.estimatedDuration,
          resourceRequirements: { ...task.resourceRequirements },
          dependencies: task.dependencies.filter(dep => !processed.has(dep))
        };
      }
      
      processed.add(task.id);
    }
    
    if (currentGroup.tasks.length > 0) {
      groups.push(currentGroup);
    }
    
    return groups;
  }

  private topologicalSort(tasks: ParallelTask[], dependencyGraph: Map<string, string[]>): ParallelTask[] {
    const inDegree = new Map<string, number>();
    const taskMap = new Map<string, ParallelTask>();
    
    // Initialize
    for (const task of tasks) {
      taskMap.set(task.id, task);
      inDegree.set(task.id, task.dependencies.length);
    }
    
    const queue: ParallelTask[] = [];
    const result: ParallelTask[] = [];
    
    // Find tasks with no dependencies
    for (const task of tasks) {
      if (inDegree.get(task.id) === 0) {
        queue.push(task);
      }
    }
    
    while (queue.length > 0) {
      const task = queue.shift()!;
      result.push(task);
      
      // Update dependent tasks
      for (const otherTask of tasks) {
        if (otherTask.dependencies.includes(task.id)) {
          const newInDegree = inDegree.get(otherTask.id)! - 1;
          inDegree.set(otherTask.id, newInDegree);
          
          if (newInDegree === 0) {
            queue.push(otherTask);
          }
        }
      }
    }
    
    return result;
  }

  private canAddToGroup(task: ParallelTask, group: TaskGroup, processed: Set<string>): boolean {
    // Check if all dependencies are already processed
    return task.dependencies.every(dep => processed.has(dep));
  }

  private updateGroupResourceRequirements(group: TaskGroup, requirements: ResourceRequirements): void {
    group.resourceRequirements.cpu += requirements.cpu;
    group.resourceRequirements.memory += requirements.memory;
    group.resourceRequirements.io = Math.max(group.resourceRequirements.io, requirements.io);
    group.resourceRequirements.network = Math.max(group.resourceRequirements.network, requirements.network);
  }

  private optimizeTaskScheduling(tasks: ParallelTask[], groups: TaskGroup[]): OptimizedTask[] {
    const optimized: OptimizedTask[] = [];
    
    for (let groupIndex = 0; groupIndex < groups.length; groupIndex++) {
      const group = groups[groupIndex];
      if (!group) continue;
      
      for (let taskIndex = 0; taskIndex < group.tasks.length; taskIndex++) {
        const taskId = group.tasks[taskIndex];
        const originalTask = tasks.find(t => t.id === taskId)!;
        
        const optimizedTask: OptimizedTask = {
          ...originalTask,
          groupId: group.id,
          executionOrder: taskIndex,
          assignedResources: this.allocateResources(originalTask.resourceRequirements),
          scheduledStartTime: groupIndex * group.estimatedDuration
        };
        
        optimized.push(optimizedTask);
      }
    }
    
    return optimized;
  }

  private allocateResources(requirements: ResourceRequirements): ResourceRequirements {
    // Apply resource allocation strategy
    switch (this.strategy.resourceAllocation) {
      case 'dynamic':
        return this.dynamicResourceAllocation(requirements);
      case 'fair_share':
        return this.fairShareAllocation(requirements);
      default:
        return requirements;
    }
  }

  private dynamicResourceAllocation(requirements: ResourceRequirements): ResourceRequirements {
    // Adjust based on current system load
    const loadFactor = Math.min(1.2, Math.max(0.8, 1.0 / this.metrics.resourceUtilization));
    
    return {
      cpu: Math.min(1.0, requirements.cpu * loadFactor),
      memory: requirements.memory * loadFactor,
      io: Math.min(1.0, requirements.io * loadFactor),
      network: Math.min(1.0, requirements.network * loadFactor)
    };
  }

  private fairShareAllocation(requirements: ResourceRequirements): ResourceRequirements {
    const activeWorkers = this.activeWorkers.size;
    const fairShare = 1.0 / activeWorkers;
    
    return {
      cpu: Math.min(fairShare, requirements.cpu),
      memory: requirements.memory / activeWorkers,
      io: Math.min(fairShare, requirements.io),
      network: Math.min(fairShare, requirements.network)
    };
  }

  private calculateParallelExecutionTime(groups: TaskGroup[]): number {
    return groups.reduce((sum, group) => sum + group.estimatedDuration, 0);
  }

  private planResourceUtilization(tasks: OptimizedTask[]): ResourceUtilizationPlan {
    const totalCpu = tasks.reduce((sum, task) => sum + task.assignedResources.cpu, 0);
    const totalMemory = tasks.reduce((sum, task) => sum + task.assignedResources.memory, 0);
    const maxIo = Math.max(...tasks.map(task => task.assignedResources.io));
    const maxNetwork = Math.max(...tasks.map(task => task.assignedResources.network));
    
    const maxCores = this.strategy.maxConcurrency;
    const cpuUtilization = Math.min(1.0, totalCpu / maxCores);
    
    const bottlenecks: string[] = [];
    if (cpuUtilization > 0.9) bottlenecks.push('CPU');
    if (totalMemory > 4000) bottlenecks.push('Memory');
    if (maxIo > 0.8) bottlenecks.push('IO');
    if (maxNetwork > 0.8) bottlenecks.push('Network');
    
    return {
      cpuUtilization,
      memoryUtilization: Math.min(1.0, totalMemory / 8000), // Assume 8GB total
      ioUtilization: maxIo,
      networkUtilization: maxNetwork,
      efficiency: cpuUtilization * 0.85, // Account for overhead
      bottlenecks
    };
  }

  private async executeTaskGroupParallel<R>(group: TaskGroup, plan: ParallelizationPlan): Promise<TaskResult<R>[]> {
    const promises = group.tasks.map(async taskId => {
      const task = plan.originalTasks.find(t => t.id === taskId)!;
      await this.submitTask(task);
      return this.waitForTask<R>(taskId);
    });
    
    return Promise.all(promises);
  }

  private async executeTaskGroupSequential<R>(group: TaskGroup, plan: ParallelizationPlan): Promise<TaskResult<R>[]> {
    const results: TaskResult<R>[] = [];
    
    for (const taskId of group.tasks) {
      const task = plan.originalTasks.find(t => t.id === taskId)!;
      await this.submitTask(task);
      const result = await this.waitForTask<R>(taskId);
      results.push(result);
    }
    
    return results;
  }
}
