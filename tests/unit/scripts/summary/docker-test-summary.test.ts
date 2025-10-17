import { describe, expect, it, vi } from 'vitest';
import {
  DEFAULT_REPORT_PATH,
  DOCKER_TEST_HEADER,
  resolveReportPath,
  summarizeReport,
  summarizeSuites,
} from '../../../../scripts/summary/docker-test-summary.mjs';

describe('docker test summary script', () => {
  it('summarizes suite statuses with fallbacks', () => {
    const lines = summarizeSuites({
      api: { status: 'passed' },
      ui: {},
    });
    expect(lines).toEqual(['- api: passed', '- ui: unknown']);
  });

  it('returns placeholder when suites are empty', () => {
    expect(summarizeSuites(undefined)).toEqual(['- no suites reported']);
    expect(summarizeSuites({})).toEqual(['- no suites reported']);
  });

  it('reads report content and produces a summary string', () => {
    const stub = vi
      .fn()
      .mockReturnValue(
        JSON.stringify({ suites: { compose: { status: 'healthy' }, queue: { status: 'failed' } } }),
      );

    const summary = summarizeReport({ readFileSyncImpl: stub });
    const [resolvedPath, encoding] = stub.mock.calls[0];
    expect(resolvedPath.replace(/\\\\/g, '/')).toMatch(/reports\/consolidated-test-report\.json$/);
    expect(encoding).toBe('utf8');
    expect(summary.split('\n')).toEqual([
      DOCKER_TEST_HEADER,
      '- compose: healthy',
      '- queue: failed',
    ]);
  });

  it('allows custom report paths and propagates errors as summary text', () => {
    const stub = vi.fn(() => {
      throw new Error('boom');
    });
    const customPath = 'tmp/generated.json';
    const summary = summarizeReport({ reportPath: customPath, readFileSyncImpl: stub });
    const [resolvedPath] = stub.mock.calls[0];
    expect(resolvedPath).toBe(resolveReportPath(customPath));
    expect(summary).toBe(`${DOCKER_TEST_HEADER}\n- failed to summarize report: boom`);
  });
});
