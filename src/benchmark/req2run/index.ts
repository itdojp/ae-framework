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

// Core runner
export { BenchmarkRunner } from './runners/BenchmarkRunner.js';

// Configuration
export { 
  DEFAULT_BENCHMARK_CONFIG,
  getConfigForDifficulty,
  getConfigForCategory,
  getCIConfig
} from './config/default.js';

// Types
export * from './types/index.js';

// Version and metadata
export const BENCHMARK_VERSION = '1.0.0';
export const SUPPORTED_REQ2RUN_VERSION = '1.0.0';

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
export async function quickBenchmark(
  problemIds: string[] | 'basic' | 'intermediate' | 'advanced' | 'expert',
  options: Partial<import('./types/index.js').BenchmarkConfig> = {}
): Promise<import('./types/index.js').BenchmarkResult[]> {
  const { BenchmarkRunner } = await import('./runners/BenchmarkRunner.js');
  const { DEFAULT_BENCHMARK_CONFIG, getConfigForDifficulty } = await import('./config/default.js');
  
  let config = { ...DEFAULT_BENCHMARK_CONFIG, ...options };
  
  // Handle difficulty level shortcuts
  if (typeof problemIds === 'string') {
    const difficultyConfig = getConfigForDifficulty(problemIds as any);
    config = { ...config, ...difficultyConfig };
    problemIds = config.problems.filter(p => p.enabled).map(p => p.id);
  }
  
  const runner = new BenchmarkRunner(config);
  return await runner.runBenchmarks(problemIds);
}

/**
 * Utility function to create a CI-optimized benchmark runner
 * 
 * @example
 * ```typescript
 * const results = await createCIBenchmark().runBenchmarks(['basic-problem-001']);
 * ```
 */
export function createCIBenchmark(): any {
  const { BenchmarkRunner } = require('./runners/BenchmarkRunner.js');
  const { getCIConfig } = require('./config/default.js');
  
  return new BenchmarkRunner(getCIConfig());
}

/**
 * Get benchmark metadata and system information
 */
export async function getBenchmarkInfo(): Promise<{
  version: string;
  supportedReq2RunVersion: string;
  availableProblems: number;
  categories: string[];
  difficulties: string[];
  systemInfo: any;
}> {
  const { DEFAULT_BENCHMARK_CONFIG } = await import('./config/default.js');
  const { BenchmarkCategory, DifficultyLevel } = await import('./types/index.js');
  
  return {
    version: BENCHMARK_VERSION,
    supportedReq2RunVersion: SUPPORTED_REQ2RUN_VERSION,
    availableProblems: DEFAULT_BENCHMARK_CONFIG.problems.length,
    categories: Object.values(BenchmarkCategory),
    difficulties: Object.values(DifficultyLevel),
    systemInfo: {
      nodeVersion: process.version,
      platform: process.platform,
      arch: process.arch,
      memory: Math.round(process.memoryUsage().heapTotal / 1024 / 1024) + 'MB'
    }
  };
}