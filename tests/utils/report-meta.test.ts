import { afterEach, describe, expect, it, vi } from 'vitest';
import { buildReportMeta } from '../../src/utils/report-meta.js';

const ORIGINAL_ENV = { ...process.env };

afterEach(() => {
  process.env = { ...ORIGINAL_ENV };
  vi.restoreAllMocks();
});

describe('report-meta', () => {
  it('uses explicit options for runId and createdAt', () => {
    process.env['AE_RUN_ID'] = 'env-run';
    const meta = buildReportMeta({
      runId: 'run-123',
      createdAt: '2026-01-01T00:00:00.000Z',
    });

    expect(meta.runId).toBe('run-123');
    expect(meta.createdAt).toBe('2026-01-01T00:00:00.000Z');
  });

  it('resolves runId from preferred environment variables', () => {
    process.env['GITHUB_RUN_ID'] = 'gh-run';
    process.env['AE_RUN_ID'] = 'ae-run';
    const meta = buildReportMeta({ createdAt: '2026-01-01T00:00:00.000Z' });

    expect(meta.runId).toBe('ae-run');
  });

  it('falls back to local runId when env is missing', () => {
    delete process.env['AE_RUN_ID'];
    delete process.env['GITHUB_RUN_ID'];
    delete process.env['CI_RUN_ID'];
    delete process.env['RUN_ID'];

    vi.spyOn(Date, 'now').mockReturnValue(123456);
    const meta = buildReportMeta({ createdAt: '2026-01-01T00:00:00.000Z' });

    expect(meta.runId).toBe('local-123456');
  });

  it('prefers direct traceId env over list-based values', () => {
    process.env['AE_TRACE_ID'] = 'trace-direct';
    process.env['REPORT_ENVELOPE_TRACE_IDS'] = 'trace-list-1,trace-list-2';

    const meta = buildReportMeta({ createdAt: '2026-01-01T00:00:00.000Z' });
    expect(meta.traceId).toBe('trace-direct');
  });

  it('extracts traceId from list-based env values', () => {
    delete process.env['AE_TRACE_ID'];
    delete process.env['TRACE_ID'];
    delete process.env['REPORT_TRACE_ID'];
    process.env['REPORT_ENVELOPE_TRACE_IDS'] = '  trace-a, trace-b  trace-c';

    const meta = buildReportMeta({ createdAt: '2026-01-01T00:00:00.000Z' });
    expect(meta.traceId).toBe('trace-a');
  });

  it('captures optional environment metadata when available', () => {
    delete process.env['GITHUB_HEAD_REF'];
    delete process.env['GITHUB_REF_NAME'];
    process.env['GITHUB_SHA'] = 'abc123';
    process.env['GITHUB_REF_NAME'] = 'feature/test';
    process.env['AE_AGENT_NAME'] = 'agent-alpha';
    process.env['OPENAI_MODEL'] = 'gpt-4o-mini';

    const meta = buildReportMeta({ createdAt: '2026-01-01T00:00:00.000Z' });

    expect(meta.commitSha).toBe('abc123');
    expect(meta.branch).toBe('feature/test');
    expect(meta.agent).toBe('agent-alpha');
    expect(meta.model).toBe('gpt-4o-mini');
  });

  it('omits optional fields when env is missing', () => {
    [
      'GITHUB_SHA', 'CI_COMMIT_SHA', 'GIT_COMMIT', 'COMMIT_SHA',
      'GITHUB_HEAD_REF', 'GITHUB_REF_NAME', 'GIT_BRANCH', 'CI_COMMIT_REF_NAME', 'BRANCH_NAME',
      'AE_AGENT_NAME', 'AGENT_NAME', 'AE_AGENT', 'AGENT',
      'AE_MODEL', 'OPENAI_MODEL', 'ANTHROPIC_MODEL', 'GEMINI_MODEL', 'LLM_MODEL',
      'AE_TRACE_ID', 'TRACE_ID', 'REPORT_TRACE_ID', 'REPORT_ENVELOPE_TRACE_IDS', 'TRACE_IDS',
    ].forEach((key) => { delete process.env[key]; });

    const meta = buildReportMeta({ runId: 'run-1', createdAt: '2026-01-01T00:00:00.000Z' });
    expect(meta.commitSha).toBeUndefined();
    expect(meta.branch).toBeUndefined();
    expect(meta.agent).toBeUndefined();
    expect(meta.model).toBeUndefined();
    expect(meta.traceId).toBeUndefined();
  });
});
