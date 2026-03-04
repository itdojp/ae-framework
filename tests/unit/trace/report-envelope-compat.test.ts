import { describe, expect, it } from 'vitest';
import { toLegacyReportEnvelope } from '../../../scripts/trace/lib/report-envelope-compat.mjs';

describe('report-envelope-compat', () => {
  it('maps traceCorrelation to legacy correlation and strips unknown fields', () => {
    const current = {
      schemaVersion: '1.0.0',
      source: 'verify-lite',
      generatedAt: '2026-03-04T00:00:00.000Z',
      traceCorrelation: {
        runId: 'run-1',
        workflow: 'verify-lite',
        commit: 'abc',
        branch: 'refs/heads/main',
        traceIds: ['t-1'],
        ignored: 'x',
      },
      summary: { ok: true },
      artifacts: [
        {
          type: 'application/json',
          path: 'artifacts/verify-lite/verify-lite-run-summary.json',
          checksum: 'sha256:1111111111111111111111111111111111111111111111111111111111111111',
          extra: 'ignored',
        },
      ],
      extraRootField: 'ignored',
    };

    const legacy = toLegacyReportEnvelope(current);

    expect(legacy).toEqual({
      schemaVersion: '1.0.0',
      source: 'verify-lite',
      generatedAt: '2026-03-04T00:00:00.000Z',
      correlation: {
        runId: 'run-1',
        workflow: 'verify-lite',
        commit: 'abc',
        branch: 'refs/heads/main',
        traceIds: ['t-1'],
      },
      summary: { ok: true },
      artifacts: [
        {
          type: 'application/json',
          path: 'artifacts/verify-lite/verify-lite-run-summary.json',
          checksum: 'sha256:1111111111111111111111111111111111111111111111111111111111111111',
        },
      ],
    });
  });
});
