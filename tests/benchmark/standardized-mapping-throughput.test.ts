import { describe, it, expect } from 'vitest';
import { StandardizedBenchmarkRunner } from '../../src/benchmark/req2run/runners/StandardizedBenchmarkRunner.js';
import type { BenchmarkConfig } from '../../src/benchmark/req2run/types/index.js';

function cfg(): BenchmarkConfig {
  return {
    req2runRepository: '/tmp/req2run-benchmark',
    problems: [],
    execution: {
      parallel: false,
      maxConcurrency: 1,
      resourceLimits: { maxMemoryMB: 512, maxCpuPercent: 50, maxDiskMB: 1024, maxExecutionTimeMs: 10000 },
      environment: 'test',
      docker: { enabled: false, image: '', volumes: [], ports: [] },
    },
    evaluation: { includeCodeQualityMetrics: false, includeSecurityAnalysis: false, generateArtifacts: false },
    reporting: { formats: [], destinations: [], dashboard: { enabled: false, port: 0 } },
  } as any;
}

describe('StandardizedBenchmarkRunner mapping and throughput', () => {
  it('maps standardized phases to AEFrameworkPhase enum', () => {
    const r = new StandardizedBenchmarkRunner(cfg());
    const map = (r as any).mapStandardPhaseToLegacy.bind(r) as (name: string) => any;

    expect(map('intent')).toBeDefined();
    expect(map('requirements')).toBeDefined();
    expect(map('user-stories')).toBeDefined();
    expect(map('validation')).toBeDefined();
    expect(map('domain-modeling')).toBeDefined();
    expect(map('ui-ux-generation')).toBeDefined();
  });

  it('calculates throughput as phases per second', () => {
    const r = new StandardizedBenchmarkRunner(cfg());
    const calc = (r as any).calculateThroughput.bind(r) as (pr: any) => number;

    const pipelineResult = {
      phases: [{}, {}, {}, {}], // 4 phases
      totalDuration: 2000, // 2 seconds
    };
    const tp = calc(pipelineResult);
    expect(tp).toBeCloseTo(2.0, 3); // 4 / (2000/1000) = 2.0
  });
});

