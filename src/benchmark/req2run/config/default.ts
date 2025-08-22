/**
 * Default Req2Run Benchmark Configuration
 */

import { BenchmarkConfig, BenchmarkCategory, DifficultyLevel } from '../types/index.js';

export const DEFAULT_BENCHMARK_CONFIG: BenchmarkConfig = {
  req2runRepository: 'https://github.com/itdojp/req2run-benchmark.git',
  problems: [
    {
      id: 'web-api-basic-001',
      enabled: true,
      timeoutMs: 300000,
      retries: 1,
      category: BenchmarkCategory.WEB_API,
      difficulty: DifficultyLevel.BASIC
    }
  ],
  execution: {
    parallel: false,
    maxConcurrency: 2,
    environment: 'development'
  }
};