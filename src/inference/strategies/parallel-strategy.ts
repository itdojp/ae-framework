/**
 * Parallel Strategy for Inference Engine
 * Implements concurrent reasoning with result aggregation
 */

import { ReasoningStep, ReasoningContext, StrategyResult } from './sequential-strategy.js';

export interface ParallelTask {
  id: string;
  description: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
  dependencies: string[];
  input: any;
  estimatedDuration: number;
  maxRetries: number;
}

export interface TaskResult {
  taskId: string;
  success: boolean;
  result: any;
  duration: number;
  confidence: number;
  error?: Error;
}

export interface ParallelExecutionPlan {
  phases: TaskPhase[];
  totalTasks: number;
  estimatedDuration: number;
  resourceRequirements: string[];
}

export interface TaskPhase {
  id: string;
  tasks: ParallelTask[];
  canRunConcurrently: boolean;
  dependencies: string[];
}

export class ParallelStrategy {
  private maxConcurrency: number;
  private activeTaskCount = 0;
  private taskProcessors = new Map<string, (task: ParallelTask) => Promise<any>>();

  constructor(options: { maxConcurrency?: number } = {}) {
    this.maxConcurrency = options.maxConcurrency || 4;
    this.registerDefaultProcessors();
  }

  /**
   * Execute parallel reasoning strategy
   */
  async execute(context: ReasoningContext): Promise<StrategyResult> {
    const startTime = Date.now();
    const steps: ReasoningStep[] = [];
    const reasoning: string[] = [];

    try {
      // Create execution plan
      const plan = await this.createExecutionPlan(context);
      reasoning.push(`Created execution plan with ${plan.totalTasks} tasks in ${plan.phases.length} phases`);

      // Execute phases
      let phaseResults: Record<string, TaskResult> = {};
      
      for (const phase of plan.phases) {
        reasoning.push(`Executing phase ${phase.id} with ${phase.tasks.length} tasks`);
        
        const phaseTaskResults = await this.executePhase(phase, phaseResults, context);
        phaseResults = { ...phaseResults, ...phaseTaskResults };

        // Convert task results to reasoning steps
        for (const [taskId, taskResult] of Object.entries(phaseTaskResults)) {
          const task = phase.tasks.find(t => t.id === taskId);
          if (task) {
            const step: ReasoningStep = {
              id: taskId,
              type: this.getStepTypeFromTask(task),
              description: task.description,
              input: task.input,
              output: taskResult.result,
              confidence: taskResult.confidence,
              metadata: {
                startTime: new Date(Date.now() - taskResult.duration),
                endTime: new Date(),
                duration: taskResult.duration,
                resources: [taskId]
              }
            };
            steps.push(step);
          }
        }
      }

      // Aggregate results
      const finalResult = await this.aggregateResults(Object.values(phaseResults));
      const overallConfidence = this.calculateOverallConfidence(Object.values(phaseResults));

      reasoning.push(`Aggregated ${Object.keys(phaseResults).length} task results`);

      return {
        success: finalResult.success,
        steps,
        finalConclusion: finalResult.conclusion,
        confidence: overallConfidence,
        reasoning
      };

    } catch (error) {
      return {
        success: false,
        steps,
        finalConclusion: null,
        confidence: 0,
        reasoning: [...reasoning, `Parallel execution failed: ${(error as Error).message}`]
      };
    }
  }

  /**
   * Register a custom task processor
   */
  registerTaskProcessor(taskType: string, processor: (task: ParallelTask) => Promise<any>): void {
    this.taskProcessors.set(taskType, processor);
  }

  private registerDefaultProcessors(): void {
    this.taskProcessors.set('analyze', this.processAnalysisTask.bind(this));
    this.taskProcessors.set('validate', this.processValidationTask.bind(this));
    this.taskProcessors.set('compute', this.processComputationTask.bind(this));
    this.taskProcessors.set('fetch', this.processFetchTask.bind(this));
  }

  private async createExecutionPlan(context: ReasoningContext): Promise<ParallelExecutionPlan> {
    const tasks = this.createTasksFromContext(context);
    const phases = this.organizeTasks(tasks);
    const totalDuration = phases.reduce((sum, phase) => sum + this.estimatePhaseTime(phase), 0);
    const resourceRequirements = this.identifyResourceRequirements(tasks);

    return {
      phases,
      totalTasks: tasks.length,
      estimatedDuration: totalDuration,
      resourceRequirements
    };
  }

  private createTasksFromContext(context: ReasoningContext): ParallelTask[] {
    const tasks: ParallelTask[] = [];
    
    // Create analysis tasks for different data domains
    const dataDomains = Object.keys(context.availableData);
    for (let i = 0; i < dataDomains.length; i++) {
      const domain = dataDomains[i];
      tasks.push({
        id: `analyze-${domain}`,
        description: `Analyze data in ${domain} domain`,
        priority: 'medium',
        dependencies: [],
        input: { domain, data: context.availableData[domain] },
        estimatedDuration: 1000,
        maxRetries: 2
      });
    }

    // Create validation tasks
    for (const constraint of context.constraints) {
      tasks.push({
        id: `validate-${constraint.id || Math.random().toString(36).substr(2, 9)}`,
        description: `Validate constraint: ${constraint.description || constraint.type}`,
        priority: 'high',
        dependencies: dataDomains.map(d => `analyze-${d}`),
        input: { constraint, context },
        estimatedDuration: 500,
        maxRetries: 3
      });
    }

    // Create synthesis task
    tasks.push({
      id: 'synthesize-results',
      description: 'Synthesize all analysis and validation results',
      priority: 'critical',
      dependencies: tasks.map(t => t.id),
      input: { objectives: context.objectives },
      estimatedDuration: 800,
      maxRetries: 1
    });

    return tasks;
  }

  private organizeTasks(tasks: ParallelTask[]): TaskPhase[] {
    const phases: TaskPhase[] = [];
    const remainingTasks = [...tasks];
    let phaseId = 1;

    while (remainingTasks.length > 0) {
      const phase: TaskPhase = {
        id: `phase-${phaseId}`,
        tasks: [],
        canRunConcurrently: true,
        dependencies: []
      };

      // Find tasks with no unresolved dependencies
      const readyTasks = remainingTasks.filter(task => 
        task.dependencies.every(dep => 
          phases.some(p => p.tasks.some(t => t.id === dep))
        )
      );

      if (readyTasks.length === 0 && remainingTasks.length > 0) {
        // Break circular dependencies by taking the highest priority task
        const highestPriorityTask = remainingTasks.reduce((highest, task) => 
          this.getPriorityValue(task.priority) > this.getPriorityValue(highest.priority) ? task : highest
        );
        readyTasks.push(highestPriorityTask);
      }

      phase.tasks = readyTasks;
      phases.push(phase);

      // Remove processed tasks
      for (const task of readyTasks) {
        const index = remainingTasks.indexOf(task);
        if (index > -1) {
          remainingTasks.splice(index, 1);
        }
      }

      phaseId++;
    }

    return phases;
  }

  private async executePhase(phase: TaskPhase, previousResults: Record<string, TaskResult>, context: ReasoningContext): Promise<Record<string, TaskResult>> {
    if (!phase.canRunConcurrently || phase.tasks.length === 1) {
      // Execute tasks sequentially
      const results: Record<string, TaskResult> = {};
      for (const task of phase.tasks) {
        results[task.id] = await this.executeTask(task, previousResults, context);
      }
      return results;
    }

    // Execute tasks in parallel with concurrency limit
    const results: Record<string, TaskResult> = {};
    const taskQueue = [...phase.tasks];
    const executing: Promise<void>[] = [];

    while (taskQueue.length > 0 || executing.length > 0) {
      // Start new tasks up to concurrency limit
      while (taskQueue.length > 0 && executing.length < this.maxConcurrency) {
        const task = taskQueue.shift()!;
        const execution = this.executeTask(task, previousResults, context)
          .then(result => {
            results[task.id] = result;
          })
          .finally(() => {
            const index = executing.indexOf(execution);
            if (index > -1) executing.splice(index, 1);
          });
        executing.push(execution);
      }

      // Wait for at least one task to complete
      if (executing.length > 0) {
        await Promise.race(executing);
      }
    }

    return results;
  }

  private async executeTask(task: ParallelTask, previousResults: Record<string, TaskResult>, context: ReasoningContext): Promise<TaskResult> {
    const startTime = Date.now();
    let attempts = 0;
    let lastError: Error | undefined;

    while (attempts < task.maxRetries + 1) {
      try {
        this.activeTaskCount++;
        
        // Get processor for task
        const processor = this.getTaskProcessor(task);
        
        // Prepare task input with dependency results
        const enrichedInput = this.enrichTaskInput(task, previousResults);
        const enrichedTask = { ...task, input: enrichedInput };
        
        // Execute task
        const result = await processor(enrichedTask);
        
        this.activeTaskCount--;
        
        return {
          taskId: task.id,
          success: true,
          result,
          duration: Date.now() - startTime,
          confidence: this.calculateTaskConfidence(task, result),
          error: undefined
        };

      } catch (error) {
        this.activeTaskCount--;
        lastError = error as Error;
        attempts++;
        
        if (attempts < task.maxRetries + 1) {
          // Wait before retry
          await new Promise(resolve => setTimeout(resolve, 100 * attempts));
        }
      }
    }

    return {
      taskId: task.id,
      success: false,
      result: null,
      duration: Date.now() - startTime,
      confidence: 0,
      error: lastError
    };
  }

  private getTaskProcessor(task: ParallelTask): (task: ParallelTask) => Promise<any> {
    const taskType = task.id.split('-')[0]!;
    const processor = this.taskProcessors.get(taskType);
    
    if (!processor) {
      throw new Error(`No processor found for task type: ${taskType}`);
    }
    
    return processor;
  }

  private enrichTaskInput(task: ParallelTask, previousResults: Record<string, TaskResult>): any {
    const enrichedInput = { ...task.input };
    
    // Add dependency results
    enrichedInput.dependencyResults = {};
    for (const depId of task.dependencies) {
      if (previousResults[depId]) {
        enrichedInput.dependencyResults[depId] = previousResults[depId].result;
      }
    }
    
    return enrichedInput;
  }

  private async processAnalysisTask(task: ParallelTask): Promise<any> {
    const { domain, data } = task.input;
    
    // Simulate analysis
    await new Promise(resolve => setTimeout(resolve, Math.random() * 500 + 200));
    
    return {
      domain,
      patterns: this.extractPatterns(data),
      statistics: this.calculateStatistics(data),
      insights: [`${domain} analysis complete`]
    };
  }

  private async processValidationTask(task: ParallelTask): Promise<any> {
    const { constraint, dependencyResults } = task.input;
    
    // Simulate validation
    await new Promise(resolve => setTimeout(resolve, Math.random() * 300 + 100));
    
    const passed = Math.random() > 0.2; // 80% pass rate
    
    return {
      constraintId: constraint.id,
      passed,
      confidence: passed ? 0.85 : 0.15,
      details: `Validation ${passed ? 'passed' : 'failed'} for constraint`
    };
  }

  private async processComputationTask(task: ParallelTask): Promise<any> {
    // Simulate computation
    await new Promise(resolve => setTimeout(resolve, Math.random() * 800 + 400));
    
    return {
      computed: true,
      value: Math.random() * 100,
      metadata: { task: task.id }
    };
  }

  private async processFetchTask(task: ParallelTask): Promise<any> {
    // Simulate data fetching
    await new Promise(resolve => setTimeout(resolve, Math.random() * 600 + 300));
    
    return {
      fetched: true,
      data: { items: Math.floor(Math.random() * 20) + 1 },
      timestamp: new Date().toISOString()
    };
  }

  private async aggregateResults(results: TaskResult[]): Promise<{ success: boolean; conclusion: any }> {
    const successfulResults = results.filter(r => r.success);
    const failedResults = results.filter(r => !r.success);
    
    if (failedResults.length > successfulResults.length) {
      return {
        success: false,
        conclusion: {
          error: 'More tasks failed than succeeded',
          failureRate: failedResults.length / results.length,
          successfulTasks: successfulResults.length
        }
      };
    }
    
    return {
      success: true,
      conclusion: {
        totalTasks: results.length,
        successfulTasks: successfulResults.length,
        failedTasks: failedResults.length,
        averageConfidence: this.calculateOverallConfidence(results),
        summary: 'Parallel execution completed successfully'
      }
    };
  }

  private extractPatterns(data: any): any[] {
    if (!data || typeof data !== 'object') return [];
    
    const patterns = [];
    if (Array.isArray(data)) {
      patterns.push({ type: 'array', length: data.length });
    } else {
      patterns.push({ type: 'object', keys: Object.keys(data).length });
    }
    return patterns;
  }

  private calculateStatistics(data: any): any {
    if (Array.isArray(data)) {
      return {
        count: data.length,
        type: 'array'
      };
    } else if (typeof data === 'object' && data !== null) {
      return {
        properties: Object.keys(data).length,
        type: 'object'
      };
    }
    return { type: typeof data };
  }

  private estimatePhaseTime(phase: TaskPhase): number {
    if (!phase.canRunConcurrently) {
      return phase.tasks.reduce((sum, task) => sum + task.estimatedDuration, 0);
    }
    return Math.max(...phase.tasks.map(task => task.estimatedDuration));
  }

  private identifyResourceRequirements(tasks: ParallelTask[]): string[] {
    const resources = new Set<string>();
    for (const task of tasks) {
      resources.add('cpu');
      if (task.id.includes('fetch')) resources.add('network');
      if (task.id.includes('compute')) resources.add('memory');
    }
    return Array.from(resources);
  }

  private getPriorityValue(priority: string): number {
    switch (priority) {
      case 'critical': return 4;
      case 'high': return 3;
      case 'medium': return 2;
      case 'low': return 1;
      default: return 1;
    }
  }

  private getStepTypeFromTask(task: ParallelTask): 'analyze' | 'deduce' | 'validate' | 'synthesize' {
    if (task.id.startsWith('analyze')) return 'analyze';
    if (task.id.startsWith('validate')) return 'validate';
    if (task.id.startsWith('synthesize')) return 'synthesize';
    return 'deduce';
  }

  private calculateTaskConfidence(task: ParallelTask, result: any): number {
    let baseConfidence = 0.7;
    
    if (result && typeof result === 'object') {
      if (result.confidence !== undefined) {
        baseConfidence = result.confidence;
      } else if (result.passed === true) {
        baseConfidence = 0.8;
      } else if (result.passed === false) {
        baseConfidence = 0.3;
      }
    }
    
    // Adjust based on priority
    const priorityMultiplier = this.getPriorityValue(task.priority) / 4;
    return Math.min(1.0, baseConfidence * (0.8 + 0.2 * priorityMultiplier));
  }

  private calculateOverallConfidence(results: TaskResult[]): number {
    if (results.length === 0) return 0;
    
    const successfulResults = results.filter(r => r.success);
    if (successfulResults.length === 0) return 0;
    
    const totalConfidence = successfulResults.reduce((sum, r) => sum + r.confidence, 0);
    return totalConfidence / successfulResults.length;
  }
}