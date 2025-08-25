/**
 * Task Scheduler for Phase 3.3.2
 * Advanced task scheduling with priorities, dependencies, and resource optimization
 */
import { EventEmitter } from 'events';
import type { ParallelTask, ResourceRequirements } from './parallel-optimizer.js';
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
export type SchedulingAlgorithm = 'fcfs' | 'sjf' | 'priority' | 'round_robin' | 'multilevel' | 'cfs' | 'deadline_aware' | 'resource_aware';
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
export declare class TaskScheduler extends EventEmitter {
    private policy;
    private taskQueues;
    private activeTasks;
    private waitingTasks;
    private completedTasks;
    private metrics;
    private resourceAvailability;
    private schedulingTimer?;
    private isRunning;
    private virtualTime;
    private timeSliceCounter;
    constructor(policy?: Partial<SchedulingPolicy>);
    /**
     * Start the task scheduler
     */
    start(): void;
    /**
     * Stop the task scheduler
     */
    stop(): void;
    /**
     * Schedule a task
     */
    scheduleTask(task: ParallelTask, deadline?: Date): Promise<SchedulingDecision>;
    /**
     * Update resource availability
     */
    updateResourceAvailability(resources: Partial<ResourceAvailability>): void;
    /**
     * Get scheduling metrics
     */
    getSchedulingMetrics(): SchedulingMetrics;
    /**
     * Get current task queues status
     */
    getQueueStatus(): Array<{
        queueId: string;
        length: number;
        algorithm: string;
    }>;
    /**
     * Preempt a task
     */
    preemptTask(taskId: string, reason: string): Promise<boolean>;
    /**
     * Update scheduling policy
     */
    updatePolicy(updates: Partial<SchedulingPolicy>): void;
    /**
     * Add custom task queue
     */
    addTaskQueue(queue: TaskQueue): void;
    /**
     * Remove task queue
     */
    removeTaskQueue(queueId: string): boolean;
    /**
     * Get task by ID
     */
    getTask(taskId: string): ScheduledTask | null;
    /**
     * Cancel a scheduled task
     */
    cancelTask(taskId: string): boolean;
    private createDefaultPolicy;
    private initializeMetrics;
    private initializeResourceAvailability;
    private setupDefaultQueues;
    private startSchedulingLoop;
    private executeSchedulingCycle;
    private makeSchedulingDecision;
    private executeSchedulingDecision;
    private insertTaskIntoQueue;
    private insertByPriority;
    private insertByShortest;
    private insertByDeadline;
    private executeSchedulingAlgorithm;
    private executeTask;
    private simulateTaskExecution;
    private completeTask;
    private canSatisfyResourceRequirements;
    private allocateResources;
    private releaseResources;
    private selectQueue;
    private extractAffinityTags;
    private wouldMissDeadline;
    private estimateStartTime;
    private estimateCompletionTime;
    private optimizeResourceAllocation;
    private calculateLoadFactor;
    private processPriorityBoosting;
    private checkDeadlines;
    private handleMissedDeadline;
    private handlePreemption;
    private findLongestRunningTask;
    private processWaitingTasks;
    private reorganizeQueues;
    private findTaskInQueues;
    private updateMetrics;
    private getTotalQueuedTasks;
    private calculateThroughput;
    private calculateFairnessIndex;
}
