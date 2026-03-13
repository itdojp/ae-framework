import os from 'node:os';
import path from 'node:path';
import { describe, expect, it, vi } from 'vitest';
import {
  buildLicenseAuditSuitePlan,
  runLicenseAuditSuite,
} from '../../scripts/legal/run-license-audit-suite.mjs';

describe('license audit suite', () => {
  it('builds a deterministic plan for all legal audits', () => {
    const plan = buildLicenseAuditSuitePlan({
      rootDir: '/repo',
      outputDir: '/repo/artifacts/reference/legal',
    });

    expect(plan.map((entry) => entry.key)).toEqual([
      'scope',
      'conditional',
      'notice',
      'contributors',
      'third-party',
      'cutover',
    ]);
    expect(plan[0].args).toContain('artifacts/reference/legal/license-scope-audit.json');
    expect(plan[2].args).toEqual(
      expect.arrayContaining([
        '--scope-audit',
        'artifacts/reference/legal/license-scope-audit.json',
        '--conditional-audit',
        'artifacts/reference/legal/conditional-asset-audit.json',
      ]),
    );
    expect(plan[5].args).toEqual(
      expect.arrayContaining([
        '--notice-readiness-audit',
        'artifacts/reference/legal/notice-readiness-audit.json',
        '--contributor-readiness-audit',
        'artifacts/reference/legal/contributor-license-readiness-audit.json',
      ]),
    );
  });

  it('rewrites downstream input paths when outputDir is overridden', () => {
    const plan = buildLicenseAuditSuitePlan({
      rootDir: '/repo',
      outputDir: '/repo/tmp/legal',
    });

    expect(plan[2].args).toEqual(
      expect.arrayContaining([
        '--scope-audit',
        'tmp/legal/license-scope-audit.json',
        '--conditional-audit',
        'tmp/legal/conditional-asset-audit.json',
      ]),
    );
    expect(plan[5].args).toEqual(
      expect.arrayContaining([
        '--notice-readiness-audit',
        'tmp/legal/notice-readiness-audit.json',
        '--contributor-readiness-audit',
        'tmp/legal/contributor-license-readiness-audit.json',
      ]),
    );
  });

  it('runs all legal audit steps with the same environment', () => {
    const calls = [];
    const spawnSyncImpl = vi.fn((cmd, args, options) => {
      calls.push({ cmd, args, options });
      return { status: 0, stdout: '', stderr: '' };
    });
    const outputDir = '/tmp/ae-license-audit-suite-tests';

    const summary = runLicenseAuditSuite({
      rootDir: '/repo',
      outputDir,
      env: { ...process.env, SOURCE_DATE_EPOCH: '0' },
      spawnSyncImpl,
    });

    expect(calls).toHaveLength(6);
    expect(calls.every((call) => call.options.cwd === '/repo')).toBe(true);
    expect(calls.every((call) => call.options.env.SOURCE_DATE_EPOCH === '0')).toBe(true);
    expect(summary.sourceDateEpoch).toBe('0');
    expect(summary.steps).toHaveLength(6);
  });

  it('defaults outputDir when omitted', () => {
    const spawnSyncImpl = vi.fn(() => ({ status: 0, stdout: '', stderr: '' }));
    const rootDir = path.join(os.tmpdir(), 'ae-license-audit-suite-default-output');

    const summary = runLicenseAuditSuite({
      rootDir,
      spawnSyncImpl,
    });

    expect(summary.outputDir).toBe(path.join(rootDir, 'artifacts/reference/legal'));
    expect(spawnSyncImpl.mock.calls[0][1]).toContain('artifacts/reference/legal/license-scope-audit.json');
  });

  it('fails fast when a step fails', () => {
    const spawnSyncImpl = vi
      .fn()
      .mockReturnValueOnce({ status: 0, stdout: '', stderr: '' })
      .mockReturnValueOnce({ status: 1, stdout: '', stderr: 'boom' });
    const outputDir = '/tmp/ae-license-audit-suite-tests';

    expect(() =>
      runLicenseAuditSuite({
        rootDir: '/repo',
        outputDir,
        spawnSyncImpl,
      }),
    ).toThrow('legal audit step failed (conditional): boom');
  });

  it('includes spawn errors when a step cannot start', () => {
    const spawnSyncImpl = vi.fn(() => ({
      status: null,
      stdout: '',
      stderr: '',
      error: new Error('spawn EACCES'),
    }));

    expect(() =>
      runLicenseAuditSuite({
        rootDir: '/repo',
        outputDir: '/tmp/ae-license-audit-suite-tests',
        spawnSyncImpl,
      }),
    ).toThrow('legal audit step failed (scope): spawn EACCES');
  });
});
