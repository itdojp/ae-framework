/**
 * Parallel Optimizer for Phase 3.3.2
 * Intelligent parallel processing optimization and task distribution
 */

import { EventEmitter } from 'events';
import { Worker } from 'worker_threads';
import { cpus } from 'os';
import type {
  ExecutionBackendMode,
  OptimizationMetrics,
  OptimizationStrategy,
  OptimizedTask,
  ParallelTask,
  ParallelizationPlan,
  ResourceRequirements,
  ResourceUsage,
  ResourceUtilizationPlan,
  TaskGroup,
  TaskPriority,
  TaskResult,
} from './parallel-optimizer.types.js';

export type {
  AdaptiveScalingConfig,
  ExecutionBackendMode,
  LoadBalancingStrategy,
  OptimizationMetrics,
  OptimizationStrategy,
  OptimizedTask,
  ParallelTask,
  ParallelizationPlan,
  PriorityWeights,
  ResourceAllocationStrategy,
  ResourceRequirements,
  ResourceUsage,
  ResourceUtilizationPlan,
  TaskGroup,
  TaskPriority,
  TaskResult,
  TaskType,
} from './parallel-optimizer.types.js';

type WorkerCommandMessage = {
  type: 'execute_task';
  taskId: string;
  attempt: number;
  task: ParallelTask;
};

type WorkerResponseMessage =
  | {
      type: 'task_completed';
      taskId: string;
      attempt: number;
      result: unknown;
      executionTime: number;
      resourceUsage?: Partial<ResourceUsage>;
    }
  | {
      type: 'task_error';
      taskId: string;
      attempt: number;
      error: string;
      executionTime?: number;
    }
  | {
      type: 'task_timeout';
      taskId: string;
      attempt: number;
      executionTime?: number;
      error: string;
    };

type ManagedWorker = {
  postMessage(message: WorkerCommandMessage): void;
  terminate(): Promise<void>;
  busy: boolean;
};

const PARALLEL_TASK_WORKER_SOURCE = `
const { parentPort } = require('worker_threads');
const sleepBlocking = (ms) => {
  const duration = Math.max(0, Number(ms) || 0);
  if (duration <= 0) return;
  const buffer = new SharedArrayBuffer(4);
  const signal = new Int32Array(buffer);
  Atomics.wait(signal, 0, 0, duration);
};
parentPort.on('message', (message) => {
  if (!message || message.type !== 'execute_task') {
    return;
  }
  const startedAt = Date.now();
  try {
    const task = message.task || {};
    const metadata = task.metadata || {};
    if (metadata.forceError === true) {
      throw new Error('Forced task failure');
    }
    const rawDuration = Number(metadata.executionTimeMs ?? task.estimatedDuration ?? 0);
    const durationMs = Number.isFinite(rawDuration) ? Math.max(0, rawDuration) : 0;
    sleepBlocking(Math.min(durationMs, 300));
    const executionTime = Date.now() - startedAt;
    parentPort.postMessage({
      type: 'task_completed',
      taskId: message.taskId,
      attempt: message.attempt,
      result: { success: true },
      executionTime,
      resourceUsage: {
        cpuTime: executionTime,
        memoryPeak: Number(task.resourceRequirements?.memory ?? 0),
        ioOperations: 0,
        networkBytes: 0
      }
    });
  } catch (error) {
    parentPort.postMessage({
      type: 'task_error',
      taskId: message.taskId,
      attempt: message.attempt,
      error: error instanceof Error ? error.message : String(error),
      executionTime: Date.now() - startedAt
    });
  }
});
`;

export class ParallelOptimizer extends EventEmitter {
  private strategy: OptimizationStrategy;
  private activeWorkers = new Map<string, ManagedWorker>();
  private taskQueue: ParallelTask[] = [];
  private executingTasks = new Map<string, ParallelTask>();
  private completedTasks = new Map<string, TaskResult>();
  private workerAssignments = new Map<string, string>();
  private taskTimeouts = new Map<string, NodeJS.Timeout>();
  private taskRetryCounts = new Map<string, number>();
  private taskAttempts = new Map<string, number>();
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
    activeWorkers: 0,
    failedTasks: 0,
    retriedTasks: 0,
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
      this.clearTaskTimeout(taskId);
      this.releaseWorker(taskId);
      this.executingTasks.delete(taskId);
      this.taskRetryCounts.delete(taskId);
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
    const executionBackend = this.resolveExecutionBackendMode();
    
    return {
      name: 'Intelligent Parallel Optimization',
      description: 'Adaptive parallel processing with smart resource allocation',
      maxConcurrency: defaultConcurrency,
      executionBackend,
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

  private resolveExecutionBackendMode(): ExecutionBackendMode {
    const explicitMode = process.env['AE_PARALLEL_BACKEND'];
    if (explicitMode === 'mock' || explicitMode === 'worker_threads') {
      return explicitMode;
    }
    return process.env['NODE_ENV'] === 'test' ? 'mock' : 'worker_threads';
  }

  private setupWorkerPool(): void {
    // Initialize minimum workers
    for (let i = 0; i < this.strategy.adaptiveScaling.minWorkers; i++) {
      this.createWorker();
    }
  }

  private createWorker(): string {
    const workerId = `worker-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;

    const worker =
      this.strategy.executionBackend === 'worker_threads'
        ? this.createWorkerThreadWorker(workerId)
        : this.createMockWorker(workerId);
    this.activeWorkers.set(workerId, worker);
    this.metrics.activeWorkers = this.activeWorkers.size;
    
    console.log(`🔧 Created worker: ${workerId} (${this.strategy.executionBackend})`);
    return workerId;
  }

  private createMockWorker(workerId: string): ManagedWorker {
    return {
      busy: false,
      postMessage: (message: WorkerCommandMessage) => {
        const requestedDuration = Number(message.task.metadata['executionTimeMs'] ?? message.task.estimatedDuration);
        const durationMs = Number.isFinite(requestedDuration) ? Math.max(0, requestedDuration) : 0;
        setTimeout(() => {
          if (message.task.metadata['forceError'] === true) {
            this.handleWorkerMessage(workerId, {
              type: 'task_error',
              taskId: message.taskId,
              attempt: message.attempt,
              error: 'Forced task failure',
              executionTime: durationMs,
            });
            return;
          }
          this.handleWorkerMessage(workerId, {
            type: 'task_completed',
            taskId: message.taskId,
            attempt: message.attempt,
            result: { success: true },
            executionTime: durationMs,
            resourceUsage: {
              cpuTime: durationMs,
              memoryPeak: message.task.resourceRequirements.memory,
              ioOperations: 0,
              networkBytes: 0,
            },
          });
        }, Math.min(durationMs, 100));
      },
      terminate: async () => {
        // No-op for mock workers.
      },
    };
  }

  private createWorkerThreadWorker(workerId: string): ManagedWorker {
    const threadWorker = new Worker(PARALLEL_TASK_WORKER_SOURCE, { eval: true });
    threadWorker.on('message', (message: WorkerResponseMessage) => {
      this.handleWorkerMessage(workerId, message);
    });
    threadWorker.on('error', (error) => {
      const taskId = this.workerAssignments.get(workerId);
      if (!taskId) {
        return;
      }
      const attempt = this.taskAttempts.get(taskId) ?? 1;
      this.handleWorkerMessage(workerId, {
        type: 'task_error',
        taskId,
        attempt,
        error: error.message,
      });
    });
    threadWorker.on('exit', (code) => {
      if (code === 0) {
        return;
      }
      const taskId = this.workerAssignments.get(workerId);
      if (!taskId) {
        return;
      }
      const attempt = this.taskAttempts.get(taskId) ?? 1;
      this.handleWorkerMessage(workerId, {
        type: 'task_error',
        taskId,
        attempt,
        error: `Worker exited unexpectedly with code ${code}`,
      });
    });

    return {
      busy: false,
      postMessage: (message: WorkerCommandMessage) => {
        threadWorker.postMessage(message);
      },
      terminate: async () => {
        await threadWorker.terminate();
      },
    };
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
    for (const timer of this.taskTimeouts.values()) {
      clearTimeout(timer);
    }
    this.taskTimeouts.clear();
    this.workerAssignments.clear();
    this.taskRetryCounts.clear();
    this.taskAttempts.clear();
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
      worker.busy = true;
      this.workerAssignments.set(workerId, task.id);
      const attempt = (this.taskAttempts.get(task.id) ?? 0) + 1;
      this.taskAttempts.set(task.id, attempt);

      const timeoutMs = Math.max(1, task.timeout);
      const timeout = setTimeout(() => {
        this.handleWorkerMessage(workerId, {
          type: 'task_timeout',
          taskId: task.id,
          attempt,
          error: `Task timed out after ${timeoutMs}ms`,
          executionTime: timeoutMs,
        });
      }, timeoutMs);
      this.taskTimeouts.set(task.id, timeout);

      worker.postMessage({
        type: 'execute_task',
        taskId: task.id,
        attempt,
        task: task
      });
      
      this.emit('taskStarted', { task, workerId });
      return;
    }

    this.executingTasks.delete(task.id);
    this.taskQueue.unshift(task);
  }

  private handleWorkerMessage(workerId: string, message: WorkerResponseMessage): void {
    switch (message.type) {
      case 'task_completed':
        this.handleTaskCompleted(workerId, message);
        break;
      case 'task_error':
        this.handleTaskError(workerId, message);
        break;
      case 'task_timeout':
        this.handleTaskTimeout(workerId, message);
        break;
    }
  }

  private handleTaskCompleted(
    workerId: string,
    message: Extract<WorkerResponseMessage, { type: 'task_completed' }>,
  ): void {
    const task = this.executingTasks.get(message.taskId);
    if (!task) {
      return;
    }
    const currentAttempt = this.taskAttempts.get(message.taskId);
    if (currentAttempt !== message.attempt) {
      return;
    }

    this.clearTaskTimeout(message.taskId);
    this.releaseWorker(message.taskId);
    const retryCount = this.taskRetryCounts.get(message.taskId) ?? 0;
    const resolvedResourceUsage: ResourceUsage = {
      cpuTime: message.resourceUsage?.cpuTime ?? message.executionTime,
      memoryPeak: message.resourceUsage?.memoryPeak ?? 0,
      ioOperations: message.resourceUsage?.ioOperations ?? 0,
      networkBytes: message.resourceUsage?.networkBytes ?? 0,
    };
    this.updateResourceUsage(resolvedResourceUsage);
    const result: TaskResult = {
      taskId: message.taskId,
      status: 'completed',
      result: message.result,
      executionTime: message.executionTime,
      resourceUsage: resolvedResourceUsage,
      workerId,
      retryCount,
    };

    this.executingTasks.delete(message.taskId);
    this.taskRetryCounts.delete(message.taskId);
    this.taskAttempts.delete(message.taskId);
    this.completedTasks.set(message.taskId, result);
    
    this.emit('taskCompleted', { task, result });
  }

  private handleTaskError(
    workerId: string,
    message: Extract<WorkerResponseMessage, { type: 'task_error' }>,
  ): void {
    const task = this.executingTasks.get(message.taskId);
    if (!task) {
      return;
    }
    const currentAttempt = this.taskAttempts.get(message.taskId);
    if (currentAttempt !== message.attempt) {
      return;
    }

    this.clearTaskTimeout(message.taskId);
    this.releaseWorker(message.taskId);
    const retryCount = this.taskRetryCounts.get(message.taskId) ?? 0;
    const result: TaskResult = {
      taskId: message.taskId,
      status: 'failed',
      error: message.error,
      executionTime: message.executionTime ?? 0,
      resourceUsage: {
        cpuTime: 0,
        memoryPeak: 0,
        ioOperations: 0,
        networkBytes: 0
      },
      workerId,
      retryCount,
    };

    this.executingTasks.delete(message.taskId);
    
    // Check if task should be retried
    if (retryCount < task.maxRetries) {
      this.taskRetryCounts.set(message.taskId, retryCount + 1);
      this.taskQueue.unshift(task); // Add to front of queue for retry
      this.emit('taskRetry', { task, error: message.error, retryCount: retryCount + 1 });
      this.processTaskQueue();
    } else {
      this.taskRetryCounts.delete(message.taskId);
      this.taskAttempts.delete(message.taskId);
      this.completedTasks.set(message.taskId, result);
      this.emit('taskFailed', { task, result });
    }
  }

  private handleTaskTimeout(
    workerId: string,
    message: Extract<WorkerResponseMessage, { type: 'task_timeout' }>,
  ): void {
    const task = this.executingTasks.get(message.taskId);
    if (!task) {
      return;
    }
    const currentAttempt = this.taskAttempts.get(message.taskId);
    if (currentAttempt !== message.attempt) {
      return;
    }

    this.clearTaskTimeout(message.taskId);
    this.releaseWorker(message.taskId);
    const retryCount = this.taskRetryCounts.get(message.taskId) ?? 0;
    const result: TaskResult = {
      taskId: message.taskId,
      status: 'timeout',
      error: message.error,
      executionTime: message.executionTime ?? task.timeout,
      resourceUsage: {
        cpuTime: 0,
        memoryPeak: 0,
        ioOperations: 0,
        networkBytes: 0,
      },
      workerId,
      retryCount,
    };

    this.executingTasks.delete(message.taskId);

    if (retryCount < task.maxRetries) {
      this.taskRetryCounts.set(message.taskId, retryCount + 1);
      this.taskQueue.unshift(task);
      this.emit('taskRetry', { task, error: message.error, retryCount: retryCount + 1 });
      this.processTaskQueue();
      return;
    }

    this.taskRetryCounts.delete(message.taskId);
    this.taskAttempts.delete(message.taskId);
    this.completedTasks.set(message.taskId, result);
    this.emit('taskFailed', { task, result });
  }

  private clearTaskTimeout(taskId: string): void {
    const timeout = this.taskTimeouts.get(taskId);
    if (!timeout) {
      return;
    }
    clearTimeout(timeout);
    this.taskTimeouts.delete(taskId);
  }

  private releaseWorker(taskId: string): void {
    const workerEntry = Array.from(this.workerAssignments.entries()).find(([, assignedTaskId]) => assignedTaskId === taskId);
    if (!workerEntry) {
      return;
    }
    const [workerId] = workerEntry;
    const worker = this.activeWorkers.get(workerId);
    if (worker) {
      worker.busy = false;
    }
    this.workerAssignments.delete(workerId);
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
    return Array.from(this.activeWorkers.entries())
      .filter(([, worker]) => !worker.busy)
      .map(([workerId]) => workerId);
  }

  private updateMetrics(): void {
    const completed = this.completedTasks.size;
    const successful = Array.from(this.completedTasks.values())
      .filter(r => r.status === 'completed').length;
    const failed = Array.from(this.completedTasks.values())
      .filter((result) => result.status === 'failed' || result.status === 'timeout').length;
    const retried = Array.from(this.completedTasks.values())
      .reduce((sum, result) => sum + result.retryCount, 0);
    
    this.metrics.totalTasksProcessed = completed;
    this.metrics.successRate = completed > 0 ? successful / completed : 0;
    this.metrics.queueLength = this.taskQueue.length;
    this.metrics.activeWorkers = this.activeWorkers.size;
    this.metrics.failedTasks = failed;
    this.metrics.retriedTasks = retried;
    
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
      const workersToRemove = Array.from(this.activeWorkers.entries())
        .filter(([, worker]) => !worker.busy)
        .map(([workerId]) => workerId)
        .slice(-1);
      for (const workerId of workersToRemove) {
        const worker = this.activeWorkers.get(workerId);
        if (worker) {
          void worker.terminate();
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
      const workersToRemove = Array.from(this.activeWorkers.entries())
        .filter(([, worker]) => !worker.busy)
        .map(([workerId]) => workerId)
        .slice(Math.max(0, targetWorkers));
      for (const workerId of workersToRemove) {
        const worker = this.activeWorkers.get(workerId);
        if (worker) {
          void worker.terminate();
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
