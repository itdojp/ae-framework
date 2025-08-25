/**
 * AE Framework Pipeline Integration Example
 * Demonstrates how to use the standardized pipeline for benchmark integration
 */
/**
 * Example: Complete AE Framework Pipeline Execution
 */
export declare function runCompleteAEFrameworkPipeline(): Promise<import("../pipeline/ae-framework-pipeline.js").PipelineResult>;
/**
 * Example: Individual Phase Execution
 */
export declare function runIndividualPhaseExample(): Promise<import("../interfaces/standard-interfaces.js").PhaseResult<unknown>>;
/**
 * Example: Pipeline Capabilities Inspection
 */
export declare function inspectPipelineCapabilities(): void;
/**
 * Example: Benchmark Integration
 * Shows how to integrate with req2run-benchmark using standardized pipeline
 */
export declare function benchmarkIntegrationExample(): Promise<import("../pipeline/ae-framework-pipeline.js").PipelineResult>;
export default runCompleteAEFrameworkPipeline;
