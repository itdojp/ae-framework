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
  cpu: number;
  memory: number;
  io: number;
  network: number;
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
