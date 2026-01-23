import { describe, it, expect } from 'vitest';
import os from 'node:os';
import path from 'node:path';
import fs from 'fs/promises';

import { formatGWT } from '../utils/gwt-format';
import { StandardizedBenchmarkRunner } from '../../src/benchmark/req2run/runners/StandardizedBenchmarkRunner.js';
import {
  AEFrameworkPhase,
  BenchmarkCategory,
  DifficultyLevel,
  OutputType,
  type BenchmarkConfig,
  type BenchmarkResult,
  type RequirementSpec,
} from '../../src/benchmark/req2run/types/index.js';

function makeConfig(overrides: Partial<BenchmarkConfig> = {}): BenchmarkConfig {
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
    ...overrides,
  };
}

function makeSpec(): RequirementSpec {
  return {
    id: 'p1',
    title: 'sample',
    description: 'sample',
    category: BenchmarkCategory.WEB_API,
    difficulty: DifficultyLevel.BASIC,
    requirements: [],
    constraints: {},
    testCriteria: [],
    expectedOutput: {
      type: OutputType.APPLICATION,
      format: 'text',
      examples: [],
    },
    metadata: {
      created_by: 'test',
      created_at: new Date().toISOString(),
      category: 'web-api',
      difficulty: 'basic',
    },
  };
}

describe('StandardizedBenchmarkRunner agentic metrics', () => {
  it(
    formatGWT('pipeline result with dataFlowTrace', 'calculateBenchmarkMetrics', 'derives turns/avgLen/latency'),
    async () => {
      const runner = new StandardizedBenchmarkRunner(makeConfig());
      const calc = (runner as any).calculateBenchmarkMetrics.bind(runner) as (
        pipelineResult: any,
        spec: RequirementSpec
      ) => Promise<any>;

      const pipelineResult = {
        success: true,
        totalDuration: 1000,
        phases: [
          {
            phase: 'ui-ux-generation',
            success: false,
            data: {},
            metadata: { duration: 1000 },
            errors: [],
          },
        ],
        errors: [],
        metadata: {
          dataFlowTrace: [
            { phase: 'intent', inputSize: 10, outputSize: 100, transformations: [] },
            { phase: 'requirements', inputSize: 20, outputSize: 300, transformations: [] },
          ],
        },
      };

      const metrics = await calc(pipelineResult, makeSpec());
      expect(metrics.agentic.turns.count).toBe(2);
      expect(metrics.agentic.turns.avgLen).toBe(200);
      expect(metrics.agentic.latencyMs).toBe(1000);
      expect(metrics.agentic.tokens).toEqual({ prompt: null, completion: null, tool: null, total: null });
    }
  );

  it(
    formatGWT('benchmark result', 'generateComprehensiveReport', 'includes agentic payload in JSON report'),
    async () => {
      const reportDir = await fs.mkdtemp(path.join(os.tmpdir(), 'ae-agentic-metrics-'));
      try {
        const runner = new StandardizedBenchmarkRunner(
          makeConfig({
            reporting: {
              formats: [],
              destinations: [{ type: 'file', config: { directory: reportDir } } as any],
              dashboard: { enabled: false, port: 0 },
            },
          })
        );

        const now = new Date();
        const agentic = {
          schemaVersion: '2.0.0',
          tokens: { prompt: null, completion: null, tool: null, total: null },
          costUsd: null,
          memoryHitRatio: null,
          turns: { count: 1, avgLen: 10 },
          latencyMs: 123,
        };

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
            agentic,
            resourceUsage: { maxMemoryUsage: 0, avgCpuUsage: 0, diskIO: 0, networkIO: 0, buildTime: 0, deploymentTime: 0 },
            phaseMetrics: [
              {
                phase: AEFrameworkPhase.INTENT_ANALYSIS,
                duration: 200,
                success: true,
                outputQuality: 80,
                resourceUsage: { maxMemoryUsage: 0, avgCpuUsage: 0, diskIO: 0, networkIO: 0, buildTime: 0, deploymentTime: 0 },
              },
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

        const gen = (runner as any).generateComprehensiveReport.bind(runner) as (results: BenchmarkResult[]) => Promise<void>;
        await gen([result]);

        const files = await fs.readdir(reportDir);
        const jsonName = files.find((f) => f.startsWith('req2run-standardized-benchmark-') && f.endsWith('.json'));
        expect(jsonName).toBeTruthy();

        const payload = JSON.parse(await fs.readFile(path.join(reportDir, String(jsonName)), 'utf8'));
        expect(payload.results[0].agentic).toEqual(agentic);
      } finally {
        await fs.rm(reportDir, { recursive: true, force: true });
      }
    }
  );
});

