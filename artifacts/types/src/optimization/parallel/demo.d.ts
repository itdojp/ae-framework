/**
 * Phase 3.3.2: Parallel Processing Optimization Engine Demo
 * Interactive demonstration of parallel optimization capabilities
 */
declare class ParallelOptimizationDemo {
    private system;
    private demoTasks;
    private isRunning;
    constructor();
    /**
     * Start the demo
     */
    start(): Promise<void>;
    /**
     * Stop the demo
     */
    stop(): Promise<void>;
    /**
     * Run demonstration scenarios
     */
    private runDemoScenarios;
    /**
     * Scenario 1: Basic Parallel Processing
     */
    private scenario1_BasicParallelProcessing;
    /**
     * Scenario 2: Priority-based Scheduling
     */
    private scenario2_PriorityScheduling;
    /**
     * Scenario 3: Resource-aware Optimization
     */
    private scenario3_ResourceOptimization;
    /**
     * Scenario 4: Dependency Management
     */
    private scenario4_DependencyManagement;
    /**
     * Scenario 5: Load Balancing and Auto-scaling
     */
    private scenario5_LoadBalancing;
    /**
     * Display final comprehensive metrics
     */
    private displayFinalMetrics;
    /**
     * Setup demo tasks
     */
    private setupDemoTasks;
    /**
     * Setup event listeners for demo
     */
    private setupEventListeners;
    /**
     * Create a demo task
     */
    private createTask;
    /**
     * Wait for completion with progress indicator
     */
    private waitForCompletion;
}
export { ParallelOptimizationDemo };
