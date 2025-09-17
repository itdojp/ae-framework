/**
 * Tests for Req2Run Benchmark Runner
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { formatGWT } from '../../utils/gwt-format';
import { BenchmarkRunner } from '../../../src/benchmark/req2run/runners/BenchmarkRunner.js';
import { 
  BenchmarkConfig, 
  RequirementSpec, 
  BenchmarkCategory, 
  DifficultyLevel,
  AEFrameworkPhase 
} from '../../../src/benchmark/req2run/types/index.js';

describe('BenchmarkRunner', () => {
  let runner: BenchmarkRunner;
  let mockConfig: BenchmarkConfig;

  beforeEach(() => {
    // Create a minimal mock configuration
    mockConfig = {
      req2runRepository: 'https://github.com/itdojp/req2run-benchmark.git',
      problems: [
        {
          id: 'test-problem-001',
          enabled: true,
          timeoutMs: 60000,
          retries: 1,
          category: BenchmarkCategory.WEB_API,
          difficulty: DifficultyLevel.BASIC
        }
      ],
      execution: {
        parallel: false,
        maxConcurrency: 1,
        resourceLimits: {
          maxMemoryMB: 1024,
          maxCpuPercent: 50,
          maxDiskMB: 1024,
          maxExecutionTimeMs: 300000
        },
        environment: 'test',
        docker: {
          enabled: false,
          image: 'node:18-alpine',
          volumes: [],
          ports: []
        }
      },
      evaluation: {
        weights: {
          functional: 0.35,
          performance: 0.15,
          quality: 0.20,
          security: 0.15,
          testing: 0.15
        },
        thresholds: {
          minOverallScore: 60,
          minFunctionalCoverage: 70,
          maxResponseTime: 2000,
          minCodeQuality: 75,
          maxVulnerabilities: 5
        },
        scoring: {
          algorithm: 'weighted-average',
          penalties: {
            timeoutPenalty: 0.5,
            errorPenalty: 0.3,
            qualityPenalty: 0.2
          },
          bonuses: {
            performanceBonus: 0.1,
            qualityBonus: 0.1,
            securityBonus: 0.05
          }
        }
      },
      reporting: {
        formats: ['json'],
        destinations: [],
        dashboard: {
          enabled: false,
          port: 3001,
          refreshInterval: 30000,
          charts: []
        }
      }
    } as any;

    runner = new BenchmarkRunner(mockConfig);
  });

  describe('constructor', () => {
    it(formatGWT('constructor', 'initialize with provided configuration', 'uses given options'), () => {
      expect(runner).toBeInstanceOf(BenchmarkRunner);
    });
  });

  describe('runBenchmark', () => {
    it(formatGWT('missing problem specification', 'runBenchmark', 'returns error result structure'), async () => {
      const result = await runner.runBenchmark('non-existent-problem');
      
      expect(result.success).toBe(false);
      expect(result.problemId).toBe('non-existent-problem');
      expect(result.errors).toBeDefined();
      expect(result.errors!.length).toBeGreaterThan(0);
      expect(result.metrics.overallScore).toBe(0);
    });

    it(formatGWT('valid run call', 'runBenchmark', 'returns proper result structure'), async () => {
      const result = await runner.runBenchmark('test-problem');
      
      expect(result).toHaveProperty('problemId');
      expect(result).toHaveProperty('timestamp');
      expect(result).toHaveProperty('success');
      expect(result).toHaveProperty('metrics');
      expect(result).toHaveProperty('executionDetails');
      expect(result).toHaveProperty('generatedArtifacts');
      
      // Check metrics structure
      expect(result.metrics).toHaveProperty('overallScore');
      expect(result.metrics).toHaveProperty('functionalCoverage');
      expect(result.metrics).toHaveProperty('testPassRate');
      expect(result.metrics).toHaveProperty('performance');
      expect(result.metrics).toHaveProperty('codeQuality');
      expect(result.metrics).toHaveProperty('security');
      expect(result.metrics).toHaveProperty('timeToCompletion');
      expect(result.metrics).toHaveProperty('resourceUsage');
      
      // Check execution details
      expect(result.executionDetails).toHaveProperty('startTime');
      expect(result.executionDetails).toHaveProperty('endTime');
      expect(result.executionDetails).toHaveProperty('totalDuration');
      expect(result.executionDetails).toHaveProperty('phaseExecutions');
      expect(result.executionDetails).toHaveProperty('environment');
    });

    it(formatGWT('runBenchmark timing', 'measure execution duration', 'returns positive duration within tolerance'), async () => {
      const startTime = Date.now();
      const result = await runner.runBenchmark('test-problem');
      const endTime = Date.now();
      
      expect(result.executionDetails.totalDuration).toBeGreaterThan(0);
      expect(result.executionDetails.totalDuration).toBeLessThanOrEqual(endTime - startTime + 100); // Allow 100ms tolerance
    });
  });

  describe('runBenchmarks', () => {
    it(formatGWT('empty list', 'runBenchmarks', 'returns empty results'), async () => {
      const results = await runner.runBenchmarks([]);
      
      expect(results).toEqual([]);
    });

    it(formatGWT('sequential run', 'runBenchmarks (parallel=false)', 'runs problems in sequence'), async () => {
      const problemIds = ['problem-1', 'problem-2', 'problem-3'];
      const startTime = Date.now();
      
      const results = await runner.runBenchmarks(problemIds);
      const endTime = Date.now();
      
      expect(results).toHaveLength(3);
      expect(results.every(r => r.problemId.startsWith('problem-'))).toBe(true);
      
      // Sequential execution should take longer than parallel (basic timing check)
      expect(endTime - startTime).toBeGreaterThan(0);
    });

    it(formatGWT('parallel execution enabled', 'runBenchmarks', 'runs with specified maxConcurrency'), async () => {
      // Create config with parallel execution
      const parallelConfig = {
        ...mockConfig,
        execution: {
          ...mockConfig.execution,
          parallel: true,
          maxConcurrency: 2
        }
      };
      
      const parallelRunner = new BenchmarkRunner(parallelConfig);
      const results = await parallelRunner.runBenchmarks(['problem-1', 'problem-2']);
      
      expect(results).toHaveLength(2);
    });
  });

  describe('error handling', () => {
    it(formatGWT('phase execution errors', 'runBenchmark', 'captures errors and marks result unsuccessful'), async () => {
      const result = await runner.runBenchmark('test-problem');
      
      // Since we don't have real implementations, we expect errors
      expect(result.success).toBe(false);
      expect(result.errors).toBeDefined();
    });

    it(formatGWT('error report', 'inspect first error', 'provides message/timestamp/phase'), async () => {
      const result = await runner.runBenchmark('test-problem');
      
      if (result.errors && result.errors.length > 0) {
        const error = result.errors[0];
        expect(error.message).toBeDefined();
        expect(error.message.length).toBeGreaterThan(0);
        expect(error.timestamp).toBeInstanceOf(Date);
        expect(error.phase).toBeDefined();
      }
    });
  });

  describe('metrics collection', () => {
    it(
      formatGWT('failed execution', 'collect default metrics', 'overallScore=0 and metrics present'),
      async () => {
      const result = await runner.runBenchmark('test-problem');
      
      // Check that all metric properties are present with valid default values
      expect(typeof result.metrics.overallScore).toBe('number');
      expect(result.metrics.overallScore).toBe(0); // Default for failed execution
      
      expect(typeof result.metrics.functionalCoverage).toBe('number');
      expect(typeof result.metrics.testPassRate).toBe('number');
      
      expect(result.metrics.performance).toBeDefined();
      expect(typeof result.metrics.performance.responseTime).toBe('number');
      expect(typeof result.metrics.performance.throughput).toBe('number');
      
      expect(result.metrics.codeQuality).toBeDefined();
      expect(typeof result.metrics.codeQuality.codeComplexity).toBe('number');
      
      expect(result.metrics.security).toBeDefined();
      expect(typeof result.metrics.security.vulnerabilityCount).toBe('number');
    }
    );
  });

  describe('generated artifacts', () => {
    it(
      formatGWT('benchmark run (no generators)', 'initialize generatedArtifacts structure', 'all arrays are empty by default'),
      async () => {
      const result = await runner.runBenchmark('test-problem');
      
      expect(result.generatedArtifacts).toBeDefined();
      expect(result.generatedArtifacts.sourceCode).toEqual([]);
      expect(result.generatedArtifacts.documentation).toEqual([]);
      expect(result.generatedArtifacts.tests).toEqual([]);
      expect(result.generatedArtifacts.configuration).toEqual([]);
      expect(result.generatedArtifacts.deployment).toEqual([]);
    }
    );
  });

  describe('execution environment', () => {
    it(
      formatGWT('benchmark run', 'capture execution environment info', 'nodeVersion/platform/arch/memory/cpuCount present'),
      async () => {
      const result = await runner.runBenchmark('test-problem');
      
      expect(result.executionDetails.environment).toBeDefined();
      expect(result.executionDetails.environment.nodeVersion).toBeDefined();
      expect(result.executionDetails.environment.platform).toBeDefined();
      expect(result.executionDetails.environment.arch).toBeDefined();
      expect(typeof result.executionDetails.environment.memory).toBe('number');
      expect(typeof result.executionDetails.environment.cpuCount).toBe('number');
    }
    );
  });
});
