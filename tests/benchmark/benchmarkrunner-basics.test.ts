import { describe, it, expect } from 'vitest';
import { BenchmarkRunner } from '../../src/benchmark/req2run/runners/BenchmarkRunner.js';
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

describe('BenchmarkRunner basics', () => {
  it('provides default metrics with zeros on failure cases', () => {
    const r = new BenchmarkRunner(cfg());
    const m = (r as any).getDefaultMetrics();
    expect(m.overallScore).toBe(0);
    expect(m.performance.responseTime).toBe(0);
    expect(m.codeQuality.typeScriptErrors).toBe(0);
  });

  it('initializes empty artifacts collection', () => {
    const r = new BenchmarkRunner(cfg());
    const a = (r as any).initializeArtifacts();
    expect(a.sourceCode).toEqual([]);
    expect(a.documentation).toEqual([]);
    expect(a.tests).toEqual([]);
    expect(a.configuration).toEqual([]);
    expect(a.deployment).toEqual([]);
  });

  it('chunkArray splits inputs as expected', () => {
    const r = new BenchmarkRunner(cfg());
    const chunk = (r as any).chunkArray.bind(r) as <T>(arr: T[], size: number) => T[][];
    const arr = [1,2,3,4,5];
    expect(chunk(arr, 2)).toEqual([[1,2],[3,4],[5]]);
  });
});

