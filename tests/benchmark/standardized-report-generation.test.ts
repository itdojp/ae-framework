import { describe, expect, it } from 'vitest';

import { formatGWT } from '../utils/gwt-format';
import {
  generateCSVReport,
  generateEnhancedMarkdownReport,
  type EnhancedReportData,
} from '../../src/benchmark/req2run/runners/standardized-benchmark-report.js';
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

function makeResult(problemId: string, success: boolean, duration: number, score: number): BenchmarkResult {
  const now = new Date();
  return {
    problemId,
    timestamp: now,
    success,
    metrics: {
      overallScore: score,
      functionalCoverage: 75,
      testPassRate: 80,
      performance: { responseTime: duration, throughput: 2, memoryUsage: 10, cpuUsage: 5, diskUsage: 1 },
      codeQuality: {
        codeComplexity: 1,
        maintainabilityIndex: 80,
        testCoverage: 75,
        duplicationRatio: 0,
        lintScore: 95,
        typeScriptErrors: 0,
      },
      security: {
        vulnerabilityCount: 0,
        securityScore: 90,
        owaspCompliance: 90,
        dependencyVulnerabilities: 0,
        secretsExposed: 0,
        securityHeaders: 6,
      },
      timeToCompletion: duration,
      resourceUsage: {
        maxMemoryUsage: 10,
        avgCpuUsage: 5,
        diskIO: 0,
        networkIO: 0,
        buildTime: 0,
        deploymentTime: 0,
      },
      phaseMetrics: [],
    },
    executionDetails: {
      startTime: now,
      endTime: new Date(now.getTime() + duration),
      totalDuration: duration,
      phaseExecutions: [
        {
          phase: AEFrameworkPhase.INTENT_ANALYSIS,
          startTime: now,
          endTime: new Date(now.getTime() + duration),
          duration,
          input: {},
          output: {},
          success,
          errors: success ? [] : ['failed'],
        },
      ],
      environment: {
        nodeVersion: process.version,
        platform: process.platform,
        arch: process.arch,
        memory: 100,
        cpuCount: 1,
      },
      logs: [],
    },
    generatedArtifacts: { sourceCode: [], documentation: [], tests: [], configuration: [], deployment: [] },
    errors: success
      ? []
      : [{ phase: AEFrameworkPhase.INTENT_ANALYSIS, type: 'runtime', message: 'boom', timestamp: now }],
  };
}

describe('standardized benchmark report helpers', () => {
  it(formatGWT('benchmark result list', 'generate CSV', 'creates header and records'), () => {
    const csv = generateCSVReport([makeResult('p-1', true, 1000, 88)]);
    const lines = csv.split('\n');
    expect(lines[0]).toContain('Problem ID,Success,Score');
    expect(lines[1]).toContain('p-1,TRUE,88.0,1000,75.0,0,0');
  });

  it(formatGWT('report data', 'render markdown', 'includes summary and per-problem section'), () => {
    const result = makeResult('p-2', false, 2500, 55);
    const data: EnhancedReportData = {
      metadata: {
        timestamp: new Date().toISOString(),
        totalProblems: 1,
        successfulRuns: 0,
        failedRuns: 1,
        averageScore: 55,
        totalExecutionTime: 2500,
        framework: 'AE Framework',
        benchmarkVersion: 'req2run-benchmark',
        pipelineVersion: '1.0.0',
        agentsUsed: ['IntentAgentAdapter'],
      },
      configuration: makeConfig(),
      analytics: {
        summary: { totalProblems: 1, successRate: 0, averageScore: 55, averageExecutionTime: 2500 },
        performance: {
          fastestExecution: 2500,
          slowestExecution: 2500,
          averagePhaseTime: { INTENT_ANALYSIS: 2500 },
        },
        quality: { highScoreProblems: 0, mediumScoreProblems: 0, lowScoreProblems: 1 },
        errors: {
          totalErrors: 1,
          errorsByPhase: { INTENT_ANALYSIS: 1 },
          commonErrorPatterns: ['boom'],
        },
      },
      results: [
        {
          problemId: result.problemId,
          success: result.success,
          score: result.metrics.overallScore,
          executionTime: result.executionDetails.totalDuration,
          agentic: null,
          functionalCoverage: result.metrics.functionalCoverage,
          phases: [{ phase: 'INTENT_ANALYSIS', success: false, duration: 2500, errors: 1 }],
          errors: ['boom'],
        },
      ],
    };

    const markdown = generateEnhancedMarkdownReport(data);
    expect(markdown).toContain('# Standardized AE Framework Benchmark Report');
    expect(markdown).toContain('### p-2');
    expect(markdown).toContain('❌ Failed');
    expect(markdown).toContain('Errors by Phase');
  });
});
