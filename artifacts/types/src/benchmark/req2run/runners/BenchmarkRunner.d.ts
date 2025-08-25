/**
 * Req2Run Benchmark Runner
 * Orchestrates the execution of AE Framework against Req2Run benchmark problems
 */
import { BenchmarkResult, BenchmarkConfig } from '../types/index.js';
export declare class BenchmarkRunner {
    private config;
    private intentAgent;
    private nlpAgent;
    private storiesAgent;
    private validationAgent;
    private domainAgent;
    constructor(config: BenchmarkConfig);
    /**
     * Run a single benchmark problem
     */
    runBenchmark(problemId: string): Promise<BenchmarkResult>;
    /**
     * Run multiple benchmark problems
     */
    runBenchmarks(problemIds: string[]): Promise<BenchmarkResult[]>;
    /**
     * Execute a single phase with error handling and metrics collection
     */
    private executePhase;
    /**
     * Initialize AE Framework agents
     */
    private initializeAgents;
    /**
     * Load problem specification from Req2Run repository
     */
    private loadProblemSpec;
    /**
     * Placeholder for UI/UX generation phase
     */
    private generateUIUX;
    /**
     * Evaluate the generated application against the problem specification
     */
    private evaluateResult;
    /**
     * Collect generated artifacts from the application
     */
    private collectArtifacts;
    /**
     * Get execution environment information
     */
    private getExecutionEnvironment;
    /**
     * Get input for a specific phase
     */
    private getPhaseInput;
    /**
     * Initialize empty artifacts structure
     */
    private initializeArtifacts;
    /**
     * Get default metrics for failed executions
     */
    private getDefaultMetrics;
    /**
     * Split array into chunks of specified size
     */
    private chunkArray;
    /**
     * Generate detailed benchmark report
     */
    private generateReport;
    /**
     * Generate Markdown report
     */
    private generateMarkdownReport;
}
