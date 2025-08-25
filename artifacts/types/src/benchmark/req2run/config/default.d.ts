/**
 * Default Req2Run Benchmark Configuration
 * Provides sensible defaults for benchmark execution
 */
import { BenchmarkConfig, BenchmarkCategory, DifficultyLevel } from '../types/index.js';
export declare const DEFAULT_BENCHMARK_CONFIG: BenchmarkConfig;
/**
 * Get configuration for a specific difficulty level
 */
export declare function getConfigForDifficulty(difficulty: DifficultyLevel): Partial<BenchmarkConfig>;
/**
 * Get configuration for a specific category
 */
export declare function getConfigForCategory(category: BenchmarkCategory): Partial<BenchmarkConfig>;
/**
 * Create a minimal configuration for CI/CD environments
 */
export declare function getCIConfig(): BenchmarkConfig;
