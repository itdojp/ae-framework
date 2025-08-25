/**
 * Standardized Req2Run Benchmark Runner
 * Uses the new AE Framework standardized pipeline for consistent benchmark execution
 * This replaces the original BenchmarkRunner with standardized interfaces
 */
import { BenchmarkResult, BenchmarkConfig } from '../types/index.js';
/**
 * Standardized Benchmark Runner
 * Leverages the AE Framework standardized pipeline for consistent, maintainable benchmark execution
 */
export declare class StandardizedBenchmarkRunner {
    private config;
    private pipeline;
    constructor(config: BenchmarkConfig);
    /**
     * Run a single benchmark problem using standardized pipeline
     */
    runBenchmark(problemId: string): Promise<BenchmarkResult>;
    /**
     * Run multiple benchmark problems with standardized pipeline
     */
    runBenchmarks(problemIds: string[]): Promise<BenchmarkResult[]>;
    /**
     * Get pipeline capabilities and health status
     */
    getPipelineStatus(): {
        capabilities: Record<string, any>;
        validation: {
            valid: boolean;
            missing: string[];
            errors: string[];
        };
        health: 'healthy' | 'degraded' | 'failed';
    };
    /**
     * Initialize standardized AE Framework pipeline
     */
    private initializePipeline;
    /**
     * Load and parse problem specification from req2run-benchmark
     */
    private loadProblemSpec;
    /**
     * Normalize req2run specification to AE Framework format
     */
    private normalizeSpecification;
    /**
     * Convert req2run spec to standardized pipeline input
     */
    private convertToStandardInput;
    /**
     * Convert pipeline result to benchmark result format
     */
    private convertToBenchmarkResult;
    /**
     * Calculate comprehensive benchmark metrics from pipeline results
     */
    private calculateBenchmarkMetrics;
    /**
     * Generate comprehensive benchmark report with enhanced analytics
     */
    private generateComprehensiveReport;
    private buildDescription;
    private extractRequirements;
    private extractConstraints;
    private buildSpecificationContent;
    private mapStandardPhaseToLegacy;
    private extractPhaseInput;
    private extractGeneratedArtifacts;
    private generateSourceCodeFromUI;
    private generateComponentCode;
    private generateDocumentationFromPipeline;
    private generateREADME;
    private generateConfigurationFiles;
    private assessFunctionalCoverage;
    private assessCodeQuality;
    private calculatePerformanceScore;
    private calculateThroughput;
    private generateAnalytics;
    private calculateAveragePhaseTime;
    private analyzeErrorsByPhase;
    private identifyCommonErrors;
    private generateEnhancedMarkdownReport;
    private generateCSVReport;
    private buildErrorResult;
    private getExecutionEnvironment;
    private getSimpleEnvironment;
    private initializeArtifacts;
    private getDefaultMetrics;
    private chunkArray;
}
