import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { StandardizedBenchmarkRunner } from '../../src/benchmark/req2run/runners/StandardizedBenchmarkRunner.js';

function makeConfig(){
  return { req2runRepository: '/tmp/req2run', problems: [], execution: { parallel: false, maxConcurrency: 1, resourceLimits: { maxMemoryMB: 128, maxCpuPercent: 50, maxDiskMB: 256, maxExecutionTimeMs: 1000 }, environment: 'test', docker: { enabled: false, image: '', volumes: [], ports: [] }, retryOnFailure: false, timeout: 500 }, evaluation: { includeCodeQualityMetrics: false, includeSecurityAnalysis: false, generateArtifacts: false }, reporting: { formats: [], destinations: [], dashboard: { enabled: false, port: 0 } } } as any;
}

describe('PBT: StandardizedBenchmarkRunner.normalizeSpecification', () => {
  it('collects requirement strings from varied shapes', async () => {
    await fc.assert(fc.asyncProperty(
      fc.record({
        f1: fc.string(), f2: fc.string(),
        nfPerf: fc.string(), nfSec: fc.string()
      }),
      async ({ f1, f2, nfPerf, nfSec }) => {
        const runner = new StandardizedBenchmarkRunner(makeConfig());
        const normalize = (runner as any).normalizeSpecification.bind(runner) as (spec: unknown, id: string) => any;
        const specInput = {
          title: 'S', notes: '', category: 'cli-tool', difficulty: 'basic',
          requirements: {
            functional: [{ id: 'F1', description: f1 }, { id: 'F2', description: f2 }],
            non_functional: { performance: [nfPerf], security: [{ description: nfSec }] }
          }
        };
        const out = normalize(specInput, 'p');
        expect(Array.isArray(out.requirements)).toBe(true);
        const checks = [
          ['f1', f1],
          ['f2', f2],
          ['nfPerf', nfPerf],
          ['nfSec', nfSec],
        ] as const;
        for (const [, value] of checks) {
          const normalized = value.trim();
          if (normalized.length === 0) continue;
          expect(out.requirements).toContain(normalized);
        }
      }
    ), { numRuns: 10 });
  });
});
