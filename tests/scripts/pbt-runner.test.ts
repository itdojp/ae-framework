import path from 'node:path';
import { describe, expect, it, vi } from 'vitest';
import {
  buildVitestCommand,
  parseArgs,
  resolvePbtPlan,
  runPbt,
} from '../../scripts/testing/run-pbt.mjs';

describe('pbt runner arg parsing', () => {
  it('parses explicit config and forwards remaining args', () => {
    const parsed = parseArgs([
      'node',
      'scripts/testing/run-pbt.mjs',
      '--config',
      'custom/vitest.config.ts',
      '--reporter=dot',
    ]);

    expect(parsed.explicitConfig).toBe('custom/vitest.config.ts');
    expect(parsed.passThrough).toEqual(['--reporter=dot']);
    expect(parsed.help).toBe(false);
  });

  it('parses --config=<path> form', () => {
    const parsed = parseArgs([
      'node',
      'scripts/testing/run-pbt.mjs',
      '--config=custom/vitest.config.ts',
      '--runInBand',
    ]);

    expect(parsed.explicitConfig).toBe('custom/vitest.config.ts');
    expect(parsed.passThrough).toEqual(['--runInBand']);
  });
});

describe('pbt runner plan resolution', () => {
  it('prefers tests/property config when present', () => {
    const cwd = '/repo';
    const configPath = path.resolve(cwd, 'tests/property/vitest.config.ts');
    const plan = resolvePbtPlan({
      cwd,
      existsSyncImpl: (candidate) => candidate === configPath,
      statSyncImpl: () => ({ isDirectory: () => false }),
    });

    expect(plan.mode).toBe('config');
    if (plan.mode === 'config') {
      expect(plan.configPath).toBe(configPath);
    }
  });

  it('falls back to tests/property directory when config is missing', () => {
    const cwd = '/repo';
    const testsDir = path.resolve(cwd, 'tests/property');
    const plan = resolvePbtPlan({
      cwd,
      existsSyncImpl: (candidate) => candidate === testsDir,
      statSyncImpl: (candidate) => ({
        isDirectory: () => candidate === testsDir,
      }),
    });

    expect(plan.mode).toBe('dir');
    if (plan.mode === 'dir') {
      expect(plan.testsDir).toBe(testsDir);
    }
  });

  it('returns missing plan with searched paths when unresolved', () => {
    const plan = resolvePbtPlan({
      cwd: '/repo',
      existsSyncImpl: () => false,
      statSyncImpl: () => ({ isDirectory: () => false }),
    });

    expect(plan.mode).toBe('missing');
    if (plan.mode === 'missing') {
      expect(plan.reason).toBe('no-config-or-tests-dir');
      expect(plan.searchedPaths.length).toBeGreaterThan(1);
    }
  });
});

describe('pbt runner execution', () => {
  it('returns config-not-found code and does not spawn when plan is missing', () => {
    const spawnSyncImpl = vi.fn();
    const logger = {
      error: vi.fn(),
      log: vi.fn(),
    };

    const exitCode = runPbt(
      {
        explicitConfig: null,
        passThrough: [],
        help: false,
      },
      {
        cwd: '/repo',
        existsSyncImpl: () => false,
        spawnSyncImpl,
        logger,
      },
    );

    expect(exitCode).toBe(2);
    expect(spawnSyncImpl).not.toHaveBeenCalled();
    expect(logger.error).toHaveBeenCalledWith(expect.stringContaining('PBT_CONFIG_NOT_FOUND'));
  });

  it('forwards vitest exit code when spawned successfully', () => {
    const cwd = '/repo';
    const configPath = path.resolve(cwd, 'tests/property/vitest.config.ts');
    const spawnSyncImpl = vi.fn(() => ({ status: 1 }));

    const exitCode = runPbt(
      {
        explicitConfig: null,
        passThrough: ['--reporter=dot'],
        help: false,
      },
      {
        cwd,
        existsSyncImpl: (candidate) => candidate === configPath,
        spawnSyncImpl,
      },
    );

    expect(exitCode).toBe(1);
    expect(spawnSyncImpl).toHaveBeenCalledWith(
      'pnpm',
      expect.arrayContaining(['exec', 'vitest', 'run', '--config', 'tests/property/vitest.config.ts', '--reporter=dot']),
      expect.objectContaining({ cwd }),
    );
  });

  it('builds command from directory fallback plan', () => {
    const command = buildVitestCommand(
      {
        mode: 'dir',
        testsDir: '/repo/tests/property',
        searchedPaths: [],
      },
      ['--reporter=dot'],
      '/repo',
    );

    expect(command).toEqual({
      command: 'pnpm',
      args: ['exec', 'vitest', 'run', 'tests/property', '--reporter=dot'],
    });
  });
});
