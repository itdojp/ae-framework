/**
 * Task Scheduler for Phase 3.3.2
 * Advanced task scheduling with priorities, dependencies, and resource optimization
 */

import { EventEmitter } from 'events';
import type { ParallelTask, TaskResult, ResourceRequirements, TaskPriority } from './parallel-optimizer.js';

export interface ScheduledTask extends ParallelTask {
  scheduledTime: Date;
  deadline?: Date;
  actualStartTime?: Date;
  actualEndTime?: Date;
  queueTime: number;
  waitTime: number;
  preemptable: boolean;
  affinityTags: string[];
}

export interface SchedulingPolicy {
  algorithm: SchedulingAlgorithm;
  preemption: PreemptionPolicy;
  priorityBoost: PriorityBoostConfig;
  deadline: DeadlineHandling;
  fairness: FairnessConfig;
  optimization: SchedulingOptimization;
}

export type SchedulingAlgorithm = 
  | 'fcfs'           // First Come First Serve
  | 'sjf'            // Shortest Job First
  | 'priority'       // Priority-based
  | 'round_robin'    // Round Robin
  | 'multilevel'     // Multilevel Queue
  | 'cfs'            // Completely Fair Scheduler
  | 'deadline_aware' // Deadline-aware scheduling
  | 'resource_aware'; // Resource-aware scheduling

export interface PreemptionPolicy {
  enabled: boolean;
  strategy: 'priority_based' | 'time_slice' | 'resource_pressure' | 'deadline_pressure';
  timeSlice: number;
  priorityThreshold: number;
}

export interface PriorityBoostConfig {
  enabled: boolean;
  boostInterval: number;
  maxBoost: number;
  agingFactor: number;
}

export interface DeadlineHandling {
  strictMode: boolean;
  missedDeadlineAction: 'drop' | 'continue' | 'deprioritize';
  deadlineMargin: number;
}

export interface FairnessConfig {
  enabled: boolean;
  algorithm: 'proportional_share' | 'lottery' | 'deficit_round_robin';
  minimumShare: number;
  maxStarvationTime: number;
}

export interface SchedulingOptimization {
  loadBalancing: boolean;
  affinityOptimization: boolean;
  batchProcessing: boolean;
  adaptiveTimeSlicing: boolean;
}

export interface SchedulingMetrics {
  totalScheduled: number;
  averageWaitTime: number;
  averageResponseTime: number;
  averageTurnaroundTime: number;
  throughput: number;
  cpuUtilization: number;
  fairnessIndex: number;
  deadlineMissRate: number;
  preemptionCount: number;
  contextSwitches: number;
}

export interface TaskQueue {
  id: string;
  name: string;
  priority: number;
  tasks: ScheduledTask[];
  maxSize: number;
  timeSlice: number;
  algorithm: SchedulingAlgorithm;
}

export interface SchedulingDecision {
  taskId: string;
  action: 'schedule' | 'preempt' | 'defer' | 'reject';
  reason: string;
  estimatedStartTime: Date;
  estimatedCompletionTime: Date;
  assignedResources: ResourceRequirements;
  queueId?: string;
}

export interface ResourceAvailability {
  cpu: number;
  memory: number;
  io: number;
  network: number;
  workers: number;
  timestamp: Date;
}

export class TaskScheduler extends EventEmitter {
  private policy: SchedulingPolicy;
  private taskQueues = new Map<string, TaskQueue>();
  private activeTasks = new Map<string, ScheduledTask>();
  private waitingTasks = new Map<string, ScheduledTask>();
  private completedTasks = new Map<string, TaskResult>();
  private metrics: SchedulingMetrics;
  private resourceAvailability: ResourceAvailability;
  private schedulingTimer?: NodeJS.Timeout;
  private isRunning = false;
  private virtualTime = 0;
  private timeSliceCounter = 0;

  constructor(policy?: Partial<SchedulingPolicy>) {
    super();
    this.policy = this.createDefaultPolicy(policy);
    this.metrics = this.initializeMetrics();
    this.resourceAvailability = this.initializeResourceAvailability();
    this.setupDefaultQueues();
  }

  /**
   * Start the task scheduler
   */
  start(): void {
    if (this.isRunning) {
      return;
    }

    this.isRunning = true;
    this.startSchedulingLoop();
    this.emit('schedulerStarted');
    
    console.log(`📅 Task Scheduler started with ${this.policy.algorithm} algorithm`);
  }

  /**
   * Stop the task scheduler
   */
  stop(): void {
    if (!this.isRunning) {
      return;
    }

    this.isRunning = false;
    
    if (this.schedulingTimer) {
      clearInterval(this.schedulingTimer);
      this.schedulingTimer = undefined;
    }

    this.emit('schedulerStopped');
    console.log('📅 Task Scheduler stopped');
  }

  /**
   * Schedule a task
   */
  async scheduleTask(task: ParallelTask, deadline?: Date): Promise<SchedulingDecision> {
    const scheduledTask: ScheduledTask = {
      ...task,
      scheduledTime: new Date(),
      deadline,
      queueTime: 0,
      waitTime: 0,
      preemptable: task.priority !== 'urgent',
      affinityTags: this.extractAffinityTags(task)
    };

    const decision = this.makeSchedulingDecision(scheduledTask);
    
    switch (decision.action) {
      case 'schedule':
        await this.executeSchedulingDecision(scheduledTask, decision);
        break;
      case 'defer':
        this.waitingTasks.set(task.id, scheduledTask);
        break;
      case 'reject':
        this.emit('taskRejected', { task: scheduledTask, decision });
        break;
    }

    this.emit('schedulingDecision', { task: scheduledTask, decision });
    return decision;
  }

  /**
   * Update resource availability
   */
  updateResourceAvailability(resources: Partial<ResourceAvailability>): void {
    this.resourceAvailability = {
      ...this.resourceAvailability,
      ...resources,
      timestamp: new Date()
    };

    this.emit('resourceAvailabilityUpdated', this.resourceAvailability);
    
    // Trigger rescheduling if resources became available
    if (this.waitingTasks.size > 0) {
      this.processWaitingTasks();
    }
  }

  /**
   * Get scheduling metrics
   */
  getSchedulingMetrics(): SchedulingMetrics {
    this.updateMetrics();
    return { ...this.metrics };
  }

  /**
   * Get current task queues status
   */
  getQueueStatus(): Array<{ queueId: string; length: number; algorithm: string }> {
    return Array.from(this.taskQueues.values()).map(queue => ({
      queueId: queue.id,
      length: queue.tasks.length,
      algorithm: queue.algorithm
    }));
  }

  /**
   * Preempt a task
   */
  async preemptTask(taskId: string, reason: string): Promise<boolean> {
    const task = this.activeTasks.get(taskId);
    if (!task || !task.preemptable) {
      return false;
    }

    // Move task back to appropriate queue
    const queue = this.selectQueue(task);
    queue.tasks.unshift(task); // Add to front for priority
    
    this.activeTasks.delete(taskId);
    this.metrics.preemptionCount++;
    
    this.emit('taskPreempted', { task, reason });
    return true;
  }

  /**
   * Update scheduling policy
   */
  updatePolicy(updates: Partial<SchedulingPolicy>): void {
    this.policy = { ...this.policy, ...updates };
    this.emit('policyUpdated', this.policy);
    
    // Reorganize queues if algorithm changed
    if (updates.algorithm) {
      this.reorganizeQueues();
    }
  }

  /**
   * Add custom task queue
   */
  addTaskQueue(queue: TaskQueue): void {
    this.taskQueues.set(queue.id, queue);
    this.emit('queueAdded', queue);
  }

  /**
   * Remove task queue
   */
  removeTaskQueue(queueId: string): boolean {
    const queue = this.taskQueues.get(queueId);
    if (!queue) {
      return false;
    }

    // Move remaining tasks to default queue
    const defaultQueue = this.taskQueues.get('default')!;
    defaultQueue.tasks.push(...queue.tasks);

    this.taskQueues.delete(queueId);
    this.emit('queueRemoved', { queueId, movedTasks: queue.tasks.length });
    return true;
  }

  /**
   * Get task by ID
   */
  getTask(taskId: string): ScheduledTask | null {
    return this.activeTasks.get(taskId) || 
           this.waitingTasks.get(taskId) || 
           this.findTaskInQueues(taskId) || 
           null;
  }

  /**
   * Cancel a scheduled task
   */
  cancelTask(taskId: string): boolean {
    // Check active tasks
    if (this.activeTasks.has(taskId)) {
      this.activeTasks.delete(taskId);
      this.emit('taskCancelled', { taskId, location: 'active' });
      return true;
    }

    // Check waiting tasks
    if (this.waitingTasks.has(taskId)) {
      this.waitingTasks.delete(taskId);
      this.emit('taskCancelled', { taskId, location: 'waiting' });
      return true;
    }

    // Check queues
    for (const queue of this.taskQueues.values()) {
      const taskIndex = queue.tasks.findIndex(task => task.id === taskId);
      if (taskIndex !== -1) {
        queue.tasks.splice(taskIndex, 1);
        this.emit('taskCancelled', { taskId, location: queue.id });
        return true;
      }
    }

    return false;
  }

  // Private methods
  private createDefaultPolicy(overrides?: Partial<SchedulingPolicy>): SchedulingPolicy {
    return {
      algorithm: 'resource_aware',
      preemption: {
        enabled: true,
        strategy: 'priority_based',
        timeSlice: 1000, // 1 second
        priorityThreshold: 0.7
      },
      priorityBoost: {
        enabled: true,
        boostInterval: 5000, // 5 seconds
        maxBoost: 0.2,
        agingFactor: 0.1
      },
      deadline: {
        strictMode: false,
        missedDeadlineAction: 'continue',
        deadlineMargin: 1000 // 1 second margin
      },
      fairness: {
        enabled: true,
        algorithm: 'proportional_share',
        minimumShare: 0.1,
        maxStarvationTime: 10000 // 10 seconds
      },
      optimization: {
        loadBalancing: true,
        affinityOptimization: true,
        batchProcessing: false,
        adaptiveTimeSlicing: true
      },
      ...overrides
    };
  }

  private initializeMetrics(): SchedulingMetrics {
    return {
      totalScheduled: 0,
      averageWaitTime: 0,
      averageResponseTime: 0,
      averageTurnaroundTime: 0,
      throughput: 0,
      cpuUtilization: 0,
      fairnessIndex: 1.0,
      deadlineMissRate: 0,
      preemptionCount: 0,
      contextSwitches: 0
    };
  }

  private initializeResourceAvailability(): ResourceAvailability {
    return {
      cpu: 1.0,
      memory: 8000, // 8GB
      io: 1.0,
      network: 1.0,
      workers: 4,
      timestamp: new Date()
    };
  }

  private setupDefaultQueues(): void {
    // High priority queue
    this.taskQueues.set('high-priority', {
      id: 'high-priority',
      name: 'High Priority Queue',
      priority: 1,
      tasks: [],
      maxSize: 100,
      timeSlice: 500,
      algorithm: 'priority'
    });

    // Default queue
    this.taskQueues.set('default', {
      id: 'default',
      name: 'Default Queue',
      priority: 2,
      tasks: [],
      maxSize: 1000,
      timeSlice: 1000,
      algorithm: 'fcfs'
    });

    // Background queue
    this.taskQueues.set('background', {
      id: 'background',
      name: 'Background Queue',
      priority: 3,
      tasks: [],
      maxSize: 500,
      timeSlice: 2000,
      algorithm: 'sjf'
    });
  }

  private startSchedulingLoop(): void {
    this.schedulingTimer = setInterval(() => {
      this.executeSchedulingCycle();
      this.updateMetrics();
      this.virtualTime += 100; // Increment virtual time
    }, 100); // Run every 100ms
  }

  private executeSchedulingCycle(): void {
    // Process priority boosting
    if (this.policy.priorityBoost.enabled) {
      this.processPriorityBoosting();
    }

    // Check for deadline violations
    this.checkDeadlines();

    // Execute scheduling algorithm
    this.executeSchedulingAlgorithm();

    // Handle preemption
    if (this.policy.preemption.enabled) {
      this.handlePreemption();
    }

    // Process waiting tasks
    this.processWaitingTasks();
  }

  private makeSchedulingDecision(task: ScheduledTask): SchedulingDecision {
    const now = new Date();
    
    // Check resource requirements
    if (!this.canSatisfyResourceRequirements(task.resourceRequirements)) {
      return {
        taskId: task.id,
        action: 'defer',
        reason: 'Insufficient resources',
        estimatedStartTime: new Date(now.getTime() + 5000),
        estimatedCompletionTime: new Date(now.getTime() + 5000 + task.estimatedDuration),
        assignedResources: task.resourceRequirements
      };
    }

    // Check deadline constraints
    if (task.deadline && this.wouldMissDeadline(task)) {
      if (this.policy.deadline.strictMode) {
        return {
          taskId: task.id,
          action: 'reject',
          reason: 'Would miss deadline',
          estimatedStartTime: now,
          estimatedCompletionTime: new Date(now.getTime() + task.estimatedDuration),
          assignedResources: task.resourceRequirements
        };
      }
    }

    // Select appropriate queue
    const queue = this.selectQueue(task);
    
    return {
      taskId: task.id,
      action: 'schedule',
      reason: `Scheduled to ${queue.name}`,
      estimatedStartTime: this.estimateStartTime(task, queue),
      estimatedCompletionTime: this.estimateCompletionTime(task, queue),
      assignedResources: this.optimizeResourceAllocation(task.resourceRequirements),
      queueId: queue.id
    };
  }

  private async executeSchedulingDecision(task: ScheduledTask, decision: SchedulingDecision): Promise<void> {
    if (decision.queueId) {
      const queue = this.taskQueues.get(decision.queueId)!;
      
      // Add to queue based on algorithm
      this.insertTaskIntoQueue(task, queue);
      
      this.emit('taskQueued', { task, queue: queue.id });
    }
  }

  private insertTaskIntoQueue(task: ScheduledTask, queue: TaskQueue): void {
    switch (queue.algorithm) {
      case 'priority':
        this.insertByPriority(task, queue);
        break;
      case 'sjf':
        this.insertByShortest(task, queue);
        break;
      case 'deadline_aware':
        this.insertByDeadline(task, queue);
        break;
      default:
        queue.tasks.push(task); // FCFS
    }
  }

  private insertByPriority(task: ScheduledTask, queue: TaskQueue): void {
    const priorityValues: Record<TaskPriority, number> = {
      urgent: 5,
      high: 4,
      normal: 3,
      low: 2,
      background: 1
    };

    const taskPriority = priorityValues[task.priority];
    const insertIndex = queue.tasks.findIndex(t => 
      priorityValues[t.priority] < taskPriority
    );

    if (insertIndex === -1) {
      queue.tasks.push(task);
    } else {
      queue.tasks.splice(insertIndex, 0, task);
    }
  }

  private insertByShortest(task: ScheduledTask, queue: TaskQueue): void {
    const insertIndex = queue.tasks.findIndex(t => 
      t.estimatedDuration > task.estimatedDuration
    );

    if (insertIndex === -1) {
      queue.tasks.push(task);
    } else {
      queue.tasks.splice(insertIndex, 0, task);
    }
  }

  private insertByDeadline(task: ScheduledTask, queue: TaskQueue): void {
    if (!task.deadline) {
      queue.tasks.push(task);
      return;
    }

    const insertIndex = queue.tasks.findIndex(t => 
      !t.deadline || t.deadline > task.deadline!
    );

    if (insertIndex === -1) {
      queue.tasks.push(task);
    } else {
      queue.tasks.splice(insertIndex, 0, task);
    }
  }

  private executeSchedulingAlgorithm(): void {
    const availableResources = this.resourceAvailability;
    
    // Get next tasks to execute from each queue
    const candidates: { task: ScheduledTask; queue: TaskQueue }[] = [];
    
    for (const queue of this.taskQueues.values()) {
      if (queue.tasks.length > 0) {
        const task = queue.tasks[0];
        if (this.canSatisfyResourceRequirements(task.resourceRequirements)) {
          candidates.push({ task, queue });
        }
      }
    }

    // Sort candidates by queue priority
    candidates.sort((a, b) => a.queue.priority - b.queue.priority);

    // Execute top candidates within resource limits
    for (const candidate of candidates) {
      if (this.activeTasks.size >= availableResources.workers) {
        break;
      }

      if (this.canSatisfyResourceRequirements(candidate.task.resourceRequirements)) {
        this.executeTask(candidate.task, candidate.queue);
      }
    }
  }

  private executeTask(task: ScheduledTask, queue: TaskQueue): void {
    // Remove from queue
    const taskIndex = queue.tasks.indexOf(task);
    if (taskIndex !== -1) {
      queue.tasks.splice(taskIndex, 1);
    }

    // Mark as active
    task.actualStartTime = new Date();
    task.waitTime = task.actualStartTime.getTime() - task.scheduledTime.getTime();
    this.activeTasks.set(task.id, task);

    // Allocate resources
    this.allocateResources(task.resourceRequirements);

    this.emit('taskStarted', { task, queue: queue.id });
    
    // Simulate task execution
    this.simulateTaskExecution(task);
  }

  private simulateTaskExecution(task: ScheduledTask): void {
    // Demo simulation: uses setTimeout for simplicity
    // TODO: In production, replace with actual worker thread execution
    // or integrate with real task execution framework
    setTimeout(() => {
      this.completeTask(task);
    }, task.estimatedDuration);
  }

  private completeTask(task: ScheduledTask): void {
    task.actualEndTime = new Date();
    
    const result: TaskResult = {
      taskId: task.id,
      status: 'completed',
      result: { success: true },
      executionTime: task.actualEndTime.getTime() - task.actualStartTime!.getTime(),
      resourceUsage: {
        cpuTime: task.estimatedDuration,
        memoryPeak: task.resourceRequirements.memory,
        ioOperations: 0,
        networkBytes: 0
      },
      retryCount: 0
    };

    this.activeTasks.delete(task.id);
    this.completedTasks.set(task.id, result);
    
    // Release resources
    this.releaseResources(task.resourceRequirements);
    
    this.emit('taskCompleted', { task, result });
  }

  private canSatisfyResourceRequirements(requirements: ResourceRequirements): boolean {
    return this.resourceAvailability.cpu >= requirements.cpu &&
           this.resourceAvailability.memory >= requirements.memory &&
           this.resourceAvailability.io >= requirements.io &&
           this.resourceAvailability.network >= requirements.network;
  }

  private allocateResources(requirements: ResourceRequirements): void {
    this.resourceAvailability.cpu -= requirements.cpu;
    this.resourceAvailability.memory -= requirements.memory;
    this.resourceAvailability.io -= requirements.io;
    this.resourceAvailability.network -= requirements.network;
  }

  private releaseResources(requirements: ResourceRequirements): void {
    this.resourceAvailability.cpu += requirements.cpu;
    this.resourceAvailability.memory += requirements.memory;
    this.resourceAvailability.io += requirements.io;
    this.resourceAvailability.network += requirements.network;
    
    // Ensure we don't exceed original capacity
    this.resourceAvailability.cpu = Math.min(1.0, this.resourceAvailability.cpu);
    this.resourceAvailability.memory = Math.min(8000, this.resourceAvailability.memory);
    this.resourceAvailability.io = Math.min(1.0, this.resourceAvailability.io);
    this.resourceAvailability.network = Math.min(1.0, this.resourceAvailability.network);
  }

  private selectQueue(task: ScheduledTask): TaskQueue {
    // Select queue based on task priority and policy
    switch (task.priority) {
      case 'urgent':
      case 'high':
        return this.taskQueues.get('high-priority')!;
      case 'background':
        return this.taskQueues.get('background')!;
      default:
        return this.taskQueues.get('default')!;
    }
  }

  private extractAffinityTags(task: ParallelTask): string[] {
    const tags: string[] = [];
    
    // Extract tags from task type
    tags.push(task.type);
    
    // Extract tags from metadata
    if (task.metadata.component) {
      tags.push(`component:${task.metadata.component}`);
    }
    
    if (task.metadata.language) {
      tags.push(`language:${task.metadata.language}`);
    }
    
    return tags;
  }

  private wouldMissDeadline(task: ScheduledTask): boolean {
    if (!task.deadline) {
      return false;
    }

    const estimatedCompletionTime = Date.now() + task.estimatedDuration + 1000; // Add 1s buffer
    return estimatedCompletionTime > task.deadline.getTime();
  }

  private estimateStartTime(task: ScheduledTask, queue: TaskQueue): Date {
    const queueDelay = queue.tasks.length * 1000; // Rough estimate
    return new Date(Date.now() + queueDelay);
  }

  private estimateCompletionTime(task: ScheduledTask, queue: TaskQueue): Date {
    const startTime = this.estimateStartTime(task, queue);
    return new Date(startTime.getTime() + task.estimatedDuration);
  }

  private optimizeResourceAllocation(requirements: ResourceRequirements): ResourceRequirements {
    // Apply optimization strategies
    const loadFactor = this.calculateLoadFactor();
    
    return {
      cpu: Math.min(1.0, requirements.cpu * loadFactor),
      memory: requirements.memory * loadFactor,
      io: Math.min(1.0, requirements.io * loadFactor),
      network: Math.min(1.0, requirements.network * loadFactor)
    };
  }

  private calculateLoadFactor(): number {
    const utilization = 1.0 - this.resourceAvailability.cpu;
    return Math.max(0.5, Math.min(1.5, 1.0 / (utilization + 0.1)));
  }

  private processPriorityBoosting(): void {
    const now = Date.now();
    const boostInterval = this.policy.priorityBoost.boostInterval;
    
    for (const queue of this.taskQueues.values()) {
      for (const task of queue.tasks) {
        const waitTime = now - task.scheduledTime.getTime();
        if (waitTime > boostInterval) {
          // Boost priority (simplified implementation)
          if (task.priority === 'low') task.priority = 'normal';
          else if (task.priority === 'normal') task.priority = 'high';
        }
      }
    }
  }

  private checkDeadlines(): void {
    const now = Date.now();
    
    for (const task of this.activeTasks.values()) {
      if (task.deadline && now > task.deadline.getTime()) {
        this.handleMissedDeadline(task);
      }
    }
    
    for (const queue of this.taskQueues.values()) {
      for (let i = queue.tasks.length - 1; i >= 0; i--) {
        const task = queue.tasks[i];
        if (task.deadline && now > task.deadline.getTime()) {
          this.handleMissedDeadline(task);
          queue.tasks.splice(i, 1);
        }
      }
    }
  }

  private handleMissedDeadline(task: ScheduledTask): void {
    this.metrics.deadlineMissRate++;
    
    switch (this.policy.deadline.missedDeadlineAction) {
      case 'drop':
        this.emit('taskDropped', { task, reason: 'missed_deadline' });
        break;
      case 'deprioritize':
        task.priority = 'background';
        this.emit('taskDeprioritized', { task, reason: 'missed_deadline' });
        break;
      case 'continue':
        this.emit('deadlineMissed', { task });
        break;
    }
  }

  private handlePreemption(): void {
    if (this.policy.preemption.strategy === 'time_slice') {
      this.timeSliceCounter += 100;
      
      if (this.timeSliceCounter >= this.policy.preemption.timeSlice) {
        this.timeSliceCounter = 0;
        
        // Preempt longest running task if needed
        const longestRunningTask = this.findLongestRunningTask();
        if (longestRunningTask && longestRunningTask.preemptable) {
          this.preemptTask(longestRunningTask.id, 'time_slice_expired');
        }
      }
    }
  }

  private findLongestRunningTask(): ScheduledTask | null {
    let longestTask: ScheduledTask | null = null;
    let longestTime = 0;
    
    for (const task of this.activeTasks.values()) {
      if (task.actualStartTime) {
        const runTime = Date.now() - task.actualStartTime.getTime();
        if (runTime > longestTime) {
          longestTime = runTime;
          longestTask = task;
        }
      }
    }
    
    return longestTask;
  }

  private processWaitingTasks(): void {
    const tasksToSchedule: ScheduledTask[] = [];
    
    for (const task of this.waitingTasks.values()) {
      if (this.canSatisfyResourceRequirements(task.resourceRequirements)) {
        tasksToSchedule.push(task);
      }
    }
    
    for (const task of tasksToSchedule) {
      this.waitingTasks.delete(task.id);
      const decision = this.makeSchedulingDecision(task);
      this.executeSchedulingDecision(task, decision);
    }
  }

  private reorganizeQueues(): void {
    // Collect all tasks from all queues
    const allTasks: ScheduledTask[] = [];
    
    for (const queue of this.taskQueues.values()) {
      allTasks.push(...queue.tasks);
      queue.tasks = [];
    }
    
    // Re-schedule all tasks with new algorithm
    for (const task of allTasks) {
      const queue = this.selectQueue(task);
      this.insertTaskIntoQueue(task, queue);
    }
  }

  private findTaskInQueues(taskId: string): ScheduledTask | null {
    for (const queue of this.taskQueues.values()) {
      const task = queue.tasks.find(t => t.id === taskId);
      if (task) return task;
    }
    return null;
  }

  private updateMetrics(): void {
    const completed = this.completedTasks.size;
    const waitTimes = Array.from(this.completedTasks.values())
      .map(r => {
        const task = this.getTask(r.taskId);
        return task ? task.waitTime : 0;
      });
    
    this.metrics.totalScheduled = completed + this.activeTasks.size + this.getTotalQueuedTasks();
    this.metrics.averageWaitTime = waitTimes.length > 0 
      ? waitTimes.reduce((sum, time) => sum + time, 0) / waitTimes.length 
      : 0;
    
    // Update other metrics
    this.metrics.cpuUtilization = 1.0 - this.resourceAvailability.cpu;
    this.metrics.throughput = this.calculateThroughput();
    this.metrics.fairnessIndex = this.calculateFairnessIndex();
  }

  private getTotalQueuedTasks(): number {
    return Array.from(this.taskQueues.values())
      .reduce((sum, queue) => sum + queue.tasks.length, 0);
  }

  private calculateThroughput(): number {
    // Tasks completed in the last minute
    const oneMinuteAgo = Date.now() - 60000;
    const recentCompletions = Array.from(this.completedTasks.values())
      .filter(r => (Date.now() - r.executionTime) < 60000);
    
    return recentCompletions.length / 60; // Per second
  }

  private calculateFairnessIndex(): number {
    // Simplified fairness calculation based on wait times
    const waitTimes = Array.from(this.activeTasks.values())
      .map(task => task.waitTime);
    
    if (waitTimes.length === 0) return 1.0;
    
    const sum = waitTimes.reduce((s, t) => s + t, 0);
    const sumSquares = waitTimes.reduce((s, t) => s + t * t, 0);
    
    return waitTimes.length > 0 ? (sum * sum) / (waitTimes.length * sumSquares) : 1.0;
  }
}