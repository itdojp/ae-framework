import { describe, expect, it, vi } from 'vitest';
import {
  buildLicenseCutoverPreflightPlan,
  runLicenseCutoverPreflight,
} from '../../scripts/legal/run-license-cutover-preflight.mjs';

describe('license cutover preflight', () => {
  it('builds approval step paths from the shared output directory', () => {
    const plan = buildLicenseCutoverPreflightPlan({
      rootDir: '/repo',
      outputDir: '/repo/artifacts/reference/legal',
      approvalRecord: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
    });

    expect(plan.approval.args).toEqual(
      expect.arrayContaining([
        '--approval-record',
        'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
        '--cutover-readiness-audit',
        'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
        '--output-json',
        'artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.json',
      ]),
    );
  });

  it('rewrites approval step paths when outputDir is overridden', () => {
    const plan = buildLicenseCutoverPreflightPlan({
      rootDir: '/repo',
      outputDir: '/repo/tmp/legal',
      approvalRecord: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
    });

    expect(plan.approval.args).toEqual(
      expect.arrayContaining([
        '--cutover-readiness-audit',
        'tmp/legal/apache-license-cutover-readiness-audit.json',
        '--output-json',
        'tmp/legal/apache-license-cutover-approval-readiness-audit.json',
        '--output-md',
        'tmp/legal/apache-license-cutover-approval-readiness-audit.md',
      ]),
    );
  });

  it('normalizes a relative outputDir against rootDir', () => {
    const plan = buildLicenseCutoverPreflightPlan({
      rootDir: '/repo',
      outputDir: 'tmp/legal',
      approvalRecord: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
    });

    expect(plan.outputDir).toBe('/repo/tmp/legal');
    expect(plan.approval.args).toEqual(
      expect.arrayContaining([
        '--cutover-readiness-audit',
        'tmp/legal/apache-license-cutover-readiness-audit.json',
        '--output-json',
        'tmp/legal/apache-license-cutover-approval-readiness-audit.json',
      ]),
    );
  });

  it('runs the full suite and then approval with the same environment', () => {
    const spawnSyncImpl = vi.fn(() => ({ status: 0, stdout: '', stderr: '' }));
    const runLicenseAuditSuiteImpl = vi.fn(() => ({
      rootDir: '/repo',
      outputDir: '/repo/tmp/legal',
      sourceDateEpoch: '0',
      steps: [],
    }));

    const summary = runLicenseCutoverPreflight({
      rootDir: '/repo',
      outputDir: '/repo/tmp/legal',
      approvalRecord: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      env: { ...process.env, SOURCE_DATE_EPOCH: '0' },
      spawnSyncImpl,
      runLicenseAuditSuiteImpl,
    });

    expect(runLicenseAuditSuiteImpl).toHaveBeenCalledWith(
      expect.objectContaining({
        rootDir: '/repo',
        outputDir: '/repo/tmp/legal',
      }),
    );
    expect(spawnSyncImpl).toHaveBeenCalledTimes(1);
    expect(spawnSyncImpl.mock.calls[0][2]).toEqual(
      expect.objectContaining({
        cwd: '/repo',
        encoding: 'utf8',
      }),
    );
    expect(spawnSyncImpl.mock.calls[0][2].env.SOURCE_DATE_EPOCH).toBe('0');
    expect(summary.sourceDateEpoch).toBe('0');
    expect(summary.approval.outputs.json).toBe('tmp/legal/apache-license-cutover-approval-readiness-audit.json');
  });

  it('fails fast when the approval audit fails', () => {
    const spawnSyncImpl = vi.fn(() => ({ status: 1, stdout: '', stderr: 'approval boom' }));
    const runLicenseAuditSuiteImpl = vi.fn(() => ({
      rootDir: '/repo',
      outputDir: '/repo/tmp/legal',
      sourceDateEpoch: null,
      steps: [],
    }));

    expect(() => runLicenseCutoverPreflight({
      rootDir: '/repo',
      outputDir: '/repo/tmp/legal',
      approvalRecord: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      spawnSyncImpl,
      runLicenseAuditSuiteImpl,
    })).toThrow('license cutover preflight failed (approval): approval boom');
  });
});
