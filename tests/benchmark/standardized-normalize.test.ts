import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { StandardizedBenchmarkRunner } from '../../src/benchmark/req2run/runners/StandardizedBenchmarkRunner.js';
import type { BenchmarkConfig, RequirementSpec } from '../../src/benchmark/req2run/types/index.js';

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

describe('StandardizedBenchmarkRunner.normalizeSpecification', () => {
  it(formatGWT('mixed requirement shapes', 'normalize specification', 'functional and non-functional become string[]'), () => {
    const runner = new StandardizedBenchmarkRunner(makeConfig());
    const normalize = (runner as any).normalizeSpecification.bind(runner) as (spec: unknown, id: string) => RequirementSpec;

    const specInput = {
      title: 'Sample',
      notes: 'Details',
      category: 'cli-tool',
      difficulty: 'basic',
      requirements: {
        functional: [
          { id: 'F1', description: 'Do something important', priority: 'must' },
        ],
        non_functional: {
          performance: ['Must be fast'],
          security: [{ description: 'No secrets in logs' }],
        },
      },
      constraints: { allowed_packages: ['react'], platform: ['node'] },
      metadata: { author: 'tester', created_date: '2025-01-01T00:00:00.000Z' },
    };

    const out = normalize(specInput, 'prob-1');
    expect(out.id).toBe('prob-1');
    expect(Array.isArray(out.requirements)).toBe(true);
    expect(out.requirements).toContain('Do something important');
    expect(out.requirements).toContain('Must be fast');
    expect(out.requirements).toContain('No secrets in logs');
    expect(out.category).toBe('cli-tool');
    expect(out.difficulty).toBe('basic');
  });
});
