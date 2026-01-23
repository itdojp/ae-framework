import { describe, it, expect, beforeAll, beforeEach, afterEach } from 'vitest';

const ENV_KEYS = ['AE_PARALLEL_SUITES', 'AE_PARALLEL_EXCLUDE_SUITES'];

let savedEnv: Record<string, string | undefined> = {};
let ParallelTestCoordinator: any;

beforeAll(async () => {
  ({ ParallelTestCoordinator } = await import('../../scripts/parallel-test-coordinator.mjs'));
});

beforeEach(() => {
  savedEnv = {};
  for (const key of ENV_KEYS) {
    savedEnv[key] = process.env[key];
    delete process.env[key];
  }
});

afterEach(() => {
  for (const key of ENV_KEYS) {
    const value = savedEnv[key];
    if (value === undefined) {
      delete process.env[key];
    } else {
      process.env[key] = value;
    }
  }
});

describe('parallel-test-coordinator suite selection', () => {
  it('throws on unknown include suite name', () => {
    process.env.AE_PARALLEL_SUITES = 'unknown-suite';
    expect(() => new ParallelTestCoordinator()).toThrow(/unknown include suite/);
  });

  it('throws on unknown exclude suite name', () => {
    process.env.AE_PARALLEL_EXCLUDE_SUITES = 'unknown-suite';
    expect(() => new ParallelTestCoordinator()).toThrow(/unknown exclude suite/);
  });

  it('auto-includes dependencies for included suites', () => {
    process.env.AE_PARALLEL_SUITES = 'e2e';
    const coordinator = new ParallelTestCoordinator();
    const names = coordinator.testSuites.map((suite: any) => suite.name).sort();
    expect(names).toEqual(['e2e', 'integration', 'unit']);
  });

  it('fails fast when excludes remove a required dependency', () => {
    process.env.AE_PARALLEL_SUITES = 'integration';
    process.env.AE_PARALLEL_EXCLUDE_SUITES = 'unit';
    expect(() => new ParallelTestCoordinator()).toThrow(/requires \"unit\"/);
  });

  it('fails fast when suite selection becomes empty', () => {
    process.env.AE_PARALLEL_EXCLUDE_SUITES = 'unit,integration,quality,e2e,flake-detection';
    expect(() => new ParallelTestCoordinator()).toThrow(/no suites selected/);
  });
});

