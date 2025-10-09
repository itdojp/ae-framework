import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { StandardizedBenchmarkRunner } from '../../src/benchmark/req2run/runners/StandardizedBenchmarkRunner.js';

function makeConfig(){
  return { req2runRepository: '/tmp/req2run', problems: [], execution: { parallel: false, maxConcurrency: 1, resourceLimits: { maxMemoryMB: 128, maxCpuPercent: 50, maxDiskMB: 256, maxExecutionTimeMs: 1000 }, environment: 'test', docker: { enabled: false, image: '', volumes: [], ports: [] }, retryOnFailure: false, timeout: 500 }, evaluation: { includeCodeQualityMetrics: false, includeSecurityAnalysis: false, generateArtifacts: false }, reporting: { formats: [], destinations: [], dashboard: { enabled: false, port: 0 } } } as any;
}

describe('PBT: StandardizedBenchmarkRunner.normalizeSpecification', () => {
  it('collects requirement strings from varied shapes', async () => {
    const requirementArb = fc.string({ minLength: 1, maxLength: 120 }).filter(s => s.trim().length > 0);
    await fc.assert(fc.asyncProperty(
      fc.record({
        f1: requirementArb,
        f2: requirementArb,
        nfPerf: requirementArb,
        nfSec: requirementArb
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
        expect(out.requirements).toContain(f1.trim());
        expect(out.requirements).toContain(f2.trim());
        expect(out.requirements).toContain(nfPerf.trim());
        expect(out.requirements).toContain(nfSec.trim());
      }
    ), { numRuns: 10 });
  });
});
