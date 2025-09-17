import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { StandardizedBenchmarkRunner } from '../../src/benchmark/req2run/runners/StandardizedBenchmarkRunner.js';
import { AEFrameworkPhase, type BenchmarkConfig, type BenchmarkResult } from '../../src/benchmark/req2run/types/index.js';

function makeConfig(): BenchmarkConfig {
  return {
    req2runRepository: '/tmp/req2run-benchmark',
    problems: [],
    execution: {
      parallel: false,
      maxConcurrency: 1,
      resourceLimits: {
        maxMemoryMB: 512,
        maxCpuPercent: 50,
        maxDiskMB: 1024,
        maxExecutionTimeMs: 10000,
      },
      environment: 'test',
      docker: { enabled: false, image: '', volumes: [], ports: [] },
      retryOnFailure: false,
      timeout: 2000,
    },
    evaluation: {
      includeCodeQualityMetrics: false,
      includeSecurityAnalysis: false,
      generateArtifacts: false,
    },
    reporting: {
      formats: [],
      destinations: [],
      dashboard: { enabled: false, port: 0 },
    },
  };
}

describe('StandardizedBenchmarkRunner.generateAnalytics', () => {
  it(formatGWT('no results', 'generate analytics', 'returns empty aggregates safely'), () => {
    const runner = new StandardizedBenchmarkRunner(makeConfig());
    const gen = (runner as any).generateAnalytics.bind(runner) as (results: BenchmarkResult[]) => any;

    const a = gen([]);
    expect(a.summary.totalProblems).toBe(0);
    expect(a.summary.successRate).toBe(0);
    expect(a.performance.fastestExecution).toBe(0);
    expect(a.performance.slowestExecution).toBe(0);
  });

  it(formatGWT('single successful result', 'generate analytics', 'includes accuracy and duration aggregates'), () => {
    const runner = new StandardizedBenchmarkRunner(makeConfig());
    const gen = (runner as any).generateAnalytics.bind(runner) as (results: BenchmarkResult[]) => any;

    const now = new Date();
    const result: BenchmarkResult = {
      problemId: 'p1',
      timestamp: now,
      success: true,
      metrics: {
        overallScore: 80,
        functionalCoverage: 60,
        testPassRate: 90,
        performance: { responseTime: 1000, throughput: 10, memoryUsage: 0, cpuUsage: 0, diskUsage: 0 },
        codeQuality: { codeComplexity: 0, maintainabilityIndex: 0, testCoverage: 0, duplicationRatio: 0, lintScore: 0, typeScriptErrors: 0 },
        security: { vulnerabilityCount: 0, securityScore: 0, owaspCompliance: 0, dependencyVulnerabilities: 0, secretsExposed: 0, securityHeaders: 0 },
        timeToCompletion: 1000,
        resourceUsage: { maxMemoryUsage: 0, avgCpuUsage: 0, diskIO: 0, networkIO: 0, buildTime: 0, deploymentTime: 0 },
        phaseMetrics: [
          { phase: AEFrameworkPhase.INTENT_ANALYSIS, duration: 200, success: true, outputQuality: 80, resourceUsage: { maxMemoryUsage: 0, avgCpuUsage: 0, diskIO: 0, networkIO: 0, buildTime: 0, deploymentTime: 0 } },
        ],
      },
      executionDetails: {
        startTime: now,
        endTime: new Date(now.getTime() + 1000),
        totalDuration: 1000,
        phaseExecutions: [
          { phase: AEFrameworkPhase.INTENT_ANALYSIS, startTime: now, endTime: new Date(now.getTime() + 200), duration: 200, input: {}, output: {}, success: true },
        ],
        environment: { nodeVersion: process.version, platform: process.platform, arch: process.arch, memory: 0, cpuCount: 0 },
        logs: [],
      },
      generatedArtifacts: { sourceCode: [], documentation: [], tests: [], configuration: [], deployment: [] },
    };

    const a = gen([result]);
    expect(a.summary.totalProblems).toBe(1);
    expect(a.summary.successRate).toBe(100);
    // averageScore across successful results
    expect(Math.round(a.summary.averageScore)).toBe(80);
    // averageExecutionTime across all results
    expect(a.summary.averageExecutionTime).toBe(1000);
  });
});
