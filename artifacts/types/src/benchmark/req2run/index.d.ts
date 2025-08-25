/**
 * Req2Run Benchmark Integration - Main Entry Point
 *
 * This module provides the main exports for the AE Framework Req2Run benchmark integration.
 * It allows users to run comprehensive performance evaluations against the Req2Run benchmark
 * dataset, measuring the framework's ability to transform requirements into executable applications.
 *
 * @example
 * ```typescript
 * import { BenchmarkRunner, DEFAULT_BENCHMARK_CONFIG } from 'ae-framework/benchmark/req2run';
 *
 * const runner = new BenchmarkRunner(DEFAULT_BENCHMARK_CONFIG);
 * const result = await runner.runBenchmark('web-api-basic-001');
 * console.log(`Score: ${result.metrics.overallScore}/100`);
 * ```
 *
 * @see https://github.com/itdojp/req2run-benchmark
 * @see https://github.com/itdojp/ae-framework/issues/155
 */
export { BenchmarkRunner } from './runners/BenchmarkRunner.js';
export { DEFAULT_BENCHMARK_CONFIG, getConfigForDifficulty, getConfigForCategory, getCIConfig } from './config/default.js';
export * from './types/index.js';
export declare const BENCHMARK_VERSION = "1.0.0";
export declare const SUPPORTED_REQ2RUN_VERSION = "1.0.0";
/**
 * Quick start function for running basic benchmarks
 *
 * @param problemIds - Array of problem IDs to run, or 'basic' for basic difficulty problems
 * @param options - Optional configuration overrides
 * @returns Promise<BenchmarkResult[]>
 *
 * @example
 * ```typescript
 * // Run basic problems
 * const results = await quickBenchmark('basic');
 *
 * // Run specific problems
 * const results = await quickBenchmark(['web-api-basic-001', 'cli-tool-basic-001']);
 * ```
 */
export declare function quickBenchmark(problemIds: string[] | 'basic' | 'intermediate' | 'advanced' | 'expert', options?: Partial<import('./types/index.js').BenchmarkConfig>): Promise<import('./types/index.js').BenchmarkResult[]>;
/**
 * Utility function to create a CI-optimized benchmark runner
 *
 * @example
 * ```typescript
 * const results = await createCIBenchmark().runBenchmarks(['basic-problem-001']);
 * ```
 */
export declare function createCIBenchmark(): any;
/**
 * Get benchmark metadata and system information
 */
export declare function getBenchmarkInfo(): Promise<{
    version: string;
    supportedReq2RunVersion: string;
    availableProblems: number;
    categories: string[];
    difficulties: string[];
    systemInfo: any;
}>;
