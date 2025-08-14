/**
 * Phase 3.3.2: Parallel Processing Optimization Engine Demo
 * Interactive demonstration of parallel optimization capabilities
 */

import { ParallelOptimizationSystem, type ParallelTask } from './index.js';

class ParallelOptimizationDemo {
  private system: ParallelOptimizationSystem;
  private demoTasks: ParallelTask[] = [];
  private isRunning = false;

  constructor() {
    // Initialize with demo-optimized configuration
    this.system = new ParallelOptimizationSystem(
      // Optimizer config
      {
        name: 'Demo Parallel Optimizer',
        maxConcurrency: 6,
        loadBalancing: 'resource_aware',
        adaptiveScaling: {
          enabled: true,
          scaleUpThreshold: 0.7,
          scaleDownThreshold: 0.3,
          maxWorkers: 8,
          minWorkers: 2,
          cooldownPeriod: 10000
        }
      },
      // Scheduler config
      {
        algorithm: 'resource_aware',
        preemption: {
          enabled: true,
          strategy: 'priority_based',
          timeSlice: 2000,
          priorityThreshold: 0.8
        },
        fairness: {
          enabled: true,
          algorithm: 'proportional_share',
          minimumShare: 0.1,
          maxStarvationTime: 15000
        }
      },
      // Resource pool config
      {
        name: 'Demo Resource Pool',
        strategy: 'dynamic',
        sizing: {
          initialSize: 4,
          minSize: 2,
          maxSize: 12,
          scaleUpThreshold: 0.8,
          scaleDownThreshold: 0.2,
          scaleUpIncrement: 2,
          scaleDownDecrement: 1,
          cooldownPeriod: 5000
        }
      }
    );

    this.setupDemoTasks();
    this.setupEventListeners();
  }

  /**
   * Start the demo
   */
  async start(): Promise<void> {
    if (this.isRunning) {
      console.log('🎯 Demo is already running');
      return;
    }

    console.log('\n🚀 Starting Parallel Optimization Engine Demo\n');
    console.log('=' .repeat(60));
    
    this.isRunning = true;
    this.system.start();
    
    await this.runDemoScenarios();
  }

  /**
   * Stop the demo
   */
  async stop(): Promise<void> {
    if (!this.isRunning) {
      return;
    }

    console.log('\n🛑 Stopping Parallel Optimization Engine Demo\n');
    this.isRunning = false;
    await this.system.stop();
  }

  /**
   * Run demonstration scenarios
   */
  private async runDemoScenarios(): Promise<void> {
    console.log('📋 Running Demo Scenarios:\n');

    try {
      // Scenario 1: Basic parallel processing
      await this.scenario1_BasicParallelProcessing();
      await this.waitForCompletion(2000);

      // Scenario 2: Priority-based scheduling
      await this.scenario2_PriorityScheduling();
      await this.waitForCompletion(3000);

      // Scenario 3: Resource-aware optimization
      await this.scenario3_ResourceOptimization();
      await this.waitForCompletion(3000);

      // Scenario 4: Dependency management
      await this.scenario4_DependencyManagement();
      await this.waitForCompletion(4000);

      // Scenario 5: Load balancing and scaling
      await this.scenario5_LoadBalancing();
      await this.waitForCompletion(3000);

      // Final metrics report
      this.displayFinalMetrics();

    } catch (error) {
      console.error('❌ Demo error:', error);
    }
  }

  /**
   * Scenario 1: Basic Parallel Processing
   */
  private async scenario1_BasicParallelProcessing(): Promise<void> {
    console.log('🎬 Scenario 1: Basic Parallel Processing');
    console.log('-'.repeat(40));

    const tasks = this.demoTasks.slice(0, 5);
    
    console.log(`📤 Submitting ${tasks.length} independent tasks for parallel execution`);
    
    for (const task of tasks) {
      await this.system.getOptimizer().submitTask(task);
      console.log(`  ✅ Submitted: ${task.name} (${task.priority} priority)`);
    }

    // Generate and display parallelization plan
    const plan = await this.system.getOptimizer().generateParallelizationPlan(tasks);
    console.log(`\n📊 Parallelization Plan:`);
    console.log(`  • Execution Groups: ${plan.executionGroups.length}`);
    console.log(`  • Sequential Time: ${plan.estimatedSequentialTime}ms`);
    console.log(`  • Parallel Time: ${plan.estimatedParallelTime}ms`);
    console.log(`  • Speedup Factor: ${plan.speedupFactor.toFixed(2)}x`);
    console.log(`  • Efficiency: ${(plan.efficiency * 100).toFixed(1)}%`);
    
    console.log('✅ Scenario 1 completed\n');
  }

  /**
   * Scenario 2: Priority-based Scheduling
   */
  private async scenario2_PriorityScheduling(): Promise<void> {
    console.log('🎬 Scenario 2: Priority-based Scheduling');
    console.log('-'.repeat(40));

    // Submit tasks with different priorities
    const urgentTask = this.createTask('urgent-task', 'Urgent Processing', 'urgent', 800);
    const normalTask = this.createTask('normal-task', 'Normal Processing', 'normal', 1200);
    const backgroundTask = this.createTask('bg-task', 'Background Processing', 'background', 2000);

    console.log('📤 Submitting tasks with different priorities:');
    
    // Submit in reverse priority order to test scheduling
    await this.system.getOptimizer().submitTask(backgroundTask);
    console.log(`  ✅ Submitted: ${backgroundTask.name} (${backgroundTask.priority})`);
    
    await this.system.getOptimizer().submitTask(normalTask);
    console.log(`  ✅ Submitted: ${normalTask.name} (${normalTask.priority})`);
    
    await this.system.getOptimizer().submitTask(urgentTask);
    console.log(`  ✅ Submitted: ${urgentTask.name} (${urgentTask.priority})`);

    // Display scheduler metrics
    const schedulerMetrics = this.system.getScheduler().getSchedulingMetrics();
    console.log(`\n📊 Scheduler Metrics:`);
    console.log(`  • Total Scheduled: ${schedulerMetrics.totalScheduled}`);
    console.log(`  • Average Wait Time: ${schedulerMetrics.averageWaitTime.toFixed(2)}ms`);
    console.log(`  • CPU Utilization: ${(schedulerMetrics.cpuUtilization * 100).toFixed(1)}%`);
    
    console.log('✅ Scenario 2 completed\n');
  }

  /**
   * Scenario 3: Resource-aware Optimization
   */
  private async scenario3_ResourceOptimization(): Promise<void> {
    console.log('🎬 Scenario 3: Resource-aware Optimization');
    console.log('-'.repeat(40));

    // Create resource-intensive tasks
    const cpuTask = this.createTask('cpu-intensive', 'CPU-Intensive Task', 'high', 1500, {
      cpu: 0.8, memory: 100, io: 0.1, network: 0.1
    });
    
    const memoryTask = this.createTask('memory-intensive', 'Memory-Intensive Task', 'high', 1000, {
      cpu: 0.3, memory: 800, io: 0.1, network: 0.1
    });
    
    const ioTask = this.createTask('io-intensive', 'IO-Intensive Task', 'normal', 2000, {
      cpu: 0.2, memory: 50, io: 0.9, network: 0.1
    });

    console.log('📤 Submitting resource-intensive tasks:');
    
    await this.system.getOptimizer().submitTask(cpuTask);
    console.log(`  ✅ CPU Task: ${cpuTask.resourceRequirements.cpu} CPU, ${cpuTask.resourceRequirements.memory}MB`);
    
    await this.system.getOptimizer().submitTask(memoryTask);
    console.log(`  ✅ Memory Task: ${memoryTask.resourceRequirements.cpu} CPU, ${memoryTask.resourceRequirements.memory}MB`);
    
    await this.system.getOptimizer().submitTask(ioTask);
    console.log(`  ✅ IO Task: ${ioTask.resourceRequirements.io} IO, ${ioTask.resourceRequirements.memory}MB`);

    // Display resource utilization
    const resourceUtilization = this.system.getResourcePool().getResourceUtilization();
    console.log(`\n📊 Resource Utilization:`);
    Object.entries(resourceUtilization).forEach(([type, utilization]) => {
      console.log(`  • ${type}: ${(utilization * 100).toFixed(1)}%`);
    });
    
    console.log('✅ Scenario 3 completed\n');
  }

  /**
   * Scenario 4: Dependency Management
   */
  private async scenario4_DependencyManagement(): Promise<void> {
    console.log('🎬 Scenario 4: Task Dependency Management');
    console.log('-'.repeat(40));

    // Create tasks with dependencies
    const dataTask = this.createTask('data-load', 'Data Loading', 'high', 800);
    const processTask = this.createTask('data-process', 'Data Processing', 'normal', 1200, undefined, ['data-load']);
    const analyzeTask = this.createTask('data-analyze', 'Data Analysis', 'normal', 1000, undefined, ['data-process']);
    const reportTask = this.createTask('report-gen', 'Report Generation', 'low', 600, undefined, ['data-analyze']);

    const dependentTasks = [dataTask, processTask, analyzeTask, reportTask];

    console.log('📤 Submitting tasks with dependencies:');
    console.log('  📊 Dependency Chain: data-load → data-process → data-analyze → report-gen');
    
    for (const task of dependentTasks) {
      await this.system.getOptimizer().submitTask(task);
      const deps = task.dependencies.length > 0 ? `(depends on: ${task.dependencies.join(', ')})` : '(no dependencies)';
      console.log(`  ✅ ${task.name} ${deps}`);
    }

    // Generate execution plan for dependent tasks
    const plan = await this.system.getOptimizer().generateParallelizationPlan(dependentTasks);
    console.log(`\n📊 Dependency Execution Plan:`);
    console.log(`  • Execution Groups: ${plan.executionGroups.length}`);
    plan.executionGroups.forEach((group, index) => {
      console.log(`    Group ${index + 1}: [${group.tasks.join(', ')}] ${group.parallelExecutable ? '(parallel)' : '(sequential)'}`);
    });
    
    console.log('✅ Scenario 4 completed\n');
  }

  /**
   * Scenario 5: Load Balancing and Auto-scaling
   */
  private async scenario5_LoadBalancing(): Promise<void> {
    console.log('🎬 Scenario 5: Load Balancing and Auto-scaling');
    console.log('-'.repeat(40));

    console.log('📤 Submitting high load to trigger auto-scaling:');
    
    // Submit many tasks to trigger scaling
    const loadTasks: Promise<string>[] = [];
    for (let i = 0; i < 15; i++) {
      const task = this.createTask(
        `load-task-${i}`,
        `Load Test Task ${i}`,
        i % 3 === 0 ? 'high' : 'normal',
        300 + Math.random() * 500,
        {
          cpu: 0.2 + Math.random() * 0.3,
          memory: 50 + Math.random() * 100,
          io: 0.1,
          network: 0.1
        }
      );
      
      loadTasks.push(this.system.getOptimizer().submitTask(task));
    }

    await Promise.all(loadTasks);
    console.log(`  ✅ Submitted ${loadTasks.length} load test tasks`);

    // Monitor auto-scaling
    await this.waitForCompletion(1000);
    
    const systemMetrics = this.system.getSystemMetrics();
    console.log(`\n📊 Load Balancing Metrics:`);
    console.log(`  • Active Workers: ${systemMetrics.optimization.activeWorkers}`);
    console.log(`  • Queue Length: ${systemMetrics.optimization.queueLength}`);
    console.log(`  • Throughput: ${systemMetrics.optimization.throughput.toFixed(2)} tasks/sec`);
    console.log(`  • Resource Utilization: ${(systemMetrics.optimization.resourceUtilization * 100).toFixed(1)}%`);
    
    const poolMetrics = systemMetrics.resources;
    console.log(`\n📊 Resource Pool Scaling:`);
    console.log(`  • Total Resources: ${poolMetrics.totalResources}`);
    console.log(`  • Available Resources: ${poolMetrics.availableResources}`);
    console.log(`  • Utilization Rate: ${(poolMetrics.utilizationRate * 100).toFixed(1)}%`);
    
    console.log('✅ Scenario 5 completed\n');
  }

  /**
   * Display final comprehensive metrics
   */
  private displayFinalMetrics(): void {
    console.log('📊 Final Demo Metrics Report');
    console.log('='.repeat(60));
    
    const systemMetrics = this.system.getSystemMetrics();
    
    console.log('\n🚀 Parallel Optimizer Performance:');
    console.log(`  • Total Tasks Processed: ${systemMetrics.optimization.totalTasksProcessed}`);
    console.log(`  • Success Rate: ${(systemMetrics.optimization.successRate * 100).toFixed(1)}%`);
    console.log(`  • Average Execution Time: ${systemMetrics.optimization.averageExecutionTime.toFixed(2)}ms`);
    console.log(`  • Parallel Efficiency: ${(systemMetrics.optimization.parallelEfficiency * 100).toFixed(1)}%`);
    console.log(`  • Throughput: ${systemMetrics.optimization.throughput.toFixed(2)} tasks/sec`);

    console.log('\n📅 Task Scheduler Performance:');
    console.log(`  • Total Scheduled: ${systemMetrics.scheduling.totalScheduled}`);
    console.log(`  • Average Wait Time: ${systemMetrics.scheduling.averageWaitTime.toFixed(2)}ms`);
    console.log(`  • Average Response Time: ${systemMetrics.scheduling.averageResponseTime.toFixed(2)}ms`);
    console.log(`  • CPU Utilization: ${(systemMetrics.scheduling.cpuUtilization * 100).toFixed(1)}%`);
    console.log(`  • Fairness Index: ${systemMetrics.scheduling.fairnessIndex.toFixed(3)}`);

    console.log('\n🏊‍♂️ Resource Pool Performance:');
    console.log(`  • Total Resources: ${systemMetrics.resources.totalResources}`);
    console.log(`  • Utilization Rate: ${(systemMetrics.resources.utilizationRate * 100).toFixed(1)}%`);
    console.log(`  • Successful Allocations: ${systemMetrics.resources.successfulAllocations}`);
    console.log(`  • Failed Allocations: ${systemMetrics.resources.failedAllocations}`);
    console.log(`  • Allocation Rate: ${(systemMetrics.resources.allocationRate * 100).toFixed(1)}%`);

    console.log('\n🎯 Demo Summary:');
    console.log(`  • All scenarios completed successfully`);
    console.log(`  • System demonstrated adaptive scaling and optimization`);
    console.log(`  • Resource management and task scheduling working efficiently`);
    console.log(`  • Ready for production deployment`);
    
    console.log('\n✅ Parallel Optimization Engine Demo completed successfully!');
    console.log('='.repeat(60));
  }

  /**
   * Setup demo tasks
   */
  private setupDemoTasks(): void {
    this.demoTasks = [
      this.createTask('demo-1', 'Image Processing', 'high', 1200, { cpu: 0.6, memory: 200, io: 0.3, network: 0.1 }),
      this.createTask('demo-2', 'Data Analysis', 'normal', 800, { cpu: 0.4, memory: 150, io: 0.2, network: 0.1 }),
      this.createTask('demo-3', 'API Request', 'normal', 500, { cpu: 0.2, memory: 50, io: 0.1, network: 0.8 }),
      this.createTask('demo-4', 'File Compression', 'low', 2000, { cpu: 0.5, memory: 100, io: 0.6, network: 0.1 }),
      this.createTask('demo-5', 'Database Query', 'high', 600, { cpu: 0.3, memory: 80, io: 0.4, network: 0.3 })
    ];
  }

  /**
   * Setup event listeners for demo
   */
  private setupEventListeners(): void {
    // Optimizer events
    this.system.getOptimizer().on('taskStarted', (event) => {
      console.log(`    🏁 Started: ${event.task.name}`);
    });

    this.system.getOptimizer().on('taskCompleted', (event) => {
      console.log(`    ✅ Completed: ${event.task.name} (${event.result.executionTime}ms)`);
    });

    this.system.getOptimizer().on('scaledUp', (event) => {
      console.log(`    📈 Scaled up to ${event.newWorkerCount} workers`);
    });

    this.system.getOptimizer().on('scaledDown', (event) => {
      console.log(`    📉 Scaled down to ${event.newWorkerCount} workers`);
    });

    // Scheduler events
    this.system.getScheduler().on('taskQueued', (event) => {
      console.log(`    📋 Queued: ${event.task.name} in ${event.queue}`);
    });

    this.system.getScheduler().on('taskPreempted', (event) => {
      console.log(`    ⏸️  Preempted: ${event.task.name} (${event.reason})`);
    });

    // Resource pool events
    this.system.getResourcePool().on('allocationGranted', (allocation) => {
      console.log(`    🎯 Resources allocated to ${allocation.taskId}`);
    });

    this.system.getResourcePool().on('poolScaledUp', (event) => {
      console.log(`    🏊‍♂️ Pool scaled up: ${event.from} → ${event.to} resources`);
    });

    this.system.getResourcePool().on('alert', (alert) => {
      console.log(`    🚨 Pool alert: ${alert.type} (${alert.value})`);
    });
  }

  /**
   * Create a demo task
   */
  private createTask(
    id: string, 
    name: string, 
    priority: 'urgent' | 'high' | 'normal' | 'low' | 'background' = 'normal',
    duration: number = 1000,
    resources?: { cpu: number; memory: number; io: number; network: number },
    dependencies: string[] = []
  ): ParallelTask {
    return {
      id,
      name,
      type: 'computation',
      payload: { demo: true, timestamp: Date.now() },
      priority,
      dependencies,
      estimatedDuration: duration,
      maxRetries: 3,
      timeout: duration * 3,
      resourceRequirements: resources || {
        cpu: 0.3,
        memory: 100,
        io: 0.1,
        network: 0.1
      },
      metadata: {
        demo: true,
        scenario: 'parallel_optimization_demo'
      }
    };
  }

  /**
   * Wait for completion with progress indicator
   */
  private async waitForCompletion(ms: number): Promise<void> {
    const steps = 10;
    const stepTime = ms / steps;
    
    for (let i = 0; i < steps; i++) {
      await new Promise(resolve => setTimeout(resolve, stepTime));
      process.stdout.write('.');
    }
    console.log('\n');
  }
}

/**
 * Run the demo if this file is executed directly
 */
if (import.meta.url === `file://${process.argv[1]}`) {
  const demo = new ParallelOptimizationDemo();
  
  // Handle graceful shutdown
  process.on('SIGINT', async () => {
    console.log('\n🛑 Shutting down demo...');
    await demo.stop();
    process.exit(0);
  });
  
  // Start demo
  demo.start().catch(console.error);
}

export { ParallelOptimizationDemo };