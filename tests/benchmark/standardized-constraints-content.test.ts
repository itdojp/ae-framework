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
      resourceLimits: { maxMemoryMB: 512, maxCpuPercent: 50, maxDiskMB: 1024, maxExecutionTimeMs: 10000 },
      environment: 'test',
      docker: { enabled: false, image: '', volumes: [], ports: [] },
      retryOnFailure: false,
      timeout: 2000,
    },
    evaluation: { includeCodeQualityMetrics: false, includeSecurityAnalysis: false, generateArtifacts: false },
    reporting: { formats: [], destinations: [], dashboard: { enabled: false, port: 0 } },
  };
}

describe('StandardizedBenchmarkRunner constraints and content', () => {
  it(formatGWT('raw spec inputs', 'extractConstraints', 'maps expected keys'), () => {
    const runner = new StandardizedBenchmarkRunner(makeConfig());
    const extract = (runner as any).extractConstraints.bind(runner) as (spec: unknown) => Record<string, unknown>;

    const constraints = extract({
      constraints: { allowed_packages: ['react'], disallowed_packages: ['leftpad'], platform: ['node'] },
      requirements: { non_functional: { performance: { p95: 500 }, security: { headers: true } } }
    });

    expect(constraints.technical).toEqual(['react']);
    expect(constraints.business).toEqual(['leftpad']);
    expect((constraints.performance as any).p95).toBe(500);
    expect((constraints.security as any).headers).toBe(true);
    expect(constraints.platform).toEqual(['node']);
  });

  it(formatGWT('normalized spec', 'build content', 'renders title/description/requirements/constraints'), () => {
    const runner = new StandardizedBenchmarkRunner(makeConfig());
    const build = (runner as any).buildSpecificationContent.bind(runner) as (spec: RequirementSpec) => string;

    const spec: RequirementSpec = {
      id: 'p1',
      title: 'Demo',
      description: 'Desc',
      category:  'cli-tool' as any,
      difficulty: 'basic' as any,
      requirements: ['Do X', 'Also Y'],
      constraints: { business: ['no-vendor-lock'], performance: { p95: 300 } },
      testCriteria: [],
      expectedOutput: { type: 'application' as any, format: 'executable', examples: [] },
      metadata: { created_by: 't', created_at: new Date().toISOString(), category: 'cli-tool', difficulty: 'basic' },
    };

    const content = build(spec);
    expect(content).toContain('Demo');
    expect(content).toContain('Desc');
    expect(content).toContain('Requirements:');
    expect(content).toContain('- HIGH: Do X');
    expect(content).toContain('- HIGH: Also Y');
    expect(content).toContain('Constraints:');
    expect(content).toContain('business');
  });
});
