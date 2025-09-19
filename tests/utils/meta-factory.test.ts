import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { buildReportMeta } from '../../src/utils/meta-factory.js';
import { execSync } from 'node:child_process';

const SNAPSHOT = { ...process.env };

describe('meta-factory: buildReportMeta', () => {
  beforeEach(() => {
    process.env = { ...SNAPSHOT };
  });
  afterEach(() => {
    process.env = { ...SNAPSHOT };
  });

  it('returns full shape with env-provided fields', () => {
    process.env['AE_AGENT_NAME'] = 'agent-x';
    process.env['AE_AGENT_VERSION'] = '1.2.3';
    process.env['OPENAI_MODEL'] = 'gpt-test';
    process.env['TRACE_ID'] = 't-123';
    process.env['AE_ITERATION'] = '2';
    process.env['RUN_ID'] = 'run-42';
    process.env['GITHUB_SHA'] = '0123456789abcdef0123456789abcdef01234567';
    process.env['GITHUB_REF_NAME'] = 'feat/x';
    process.env['GITHUB_ACTIONS'] = 'true';

    const m = buildReportMeta();
    expect(m.agent.name).toBe('agent-x');
    expect(m.agent.version).toBe('1.2.3');
    expect(m.model.name).toBe('gpt-test');
    expect(m.model.provider).toBe('openai');
    expect(m.traceId).toBe('t-123');
    expect(m.iteration).toBe(2);
    expect(m.runId).toBe('run-42');
    expect(m.commitSha?.length).toBeGreaterThan(7);
    expect(m.branch).toBe('feat/x');
    expect(m.environment).toBe('github');
    expect(typeof m.createdAt).toBe('string');
  });

  it('falls back safely when env/git missing', () => {
    delete process.env['GITHUB_SHA'];
    delete process.env['CI_COMMIT_SHA'];
    delete process.env['GIT_COMMIT'];
    delete process.env['GITHUB_REF_NAME'];
    delete process.env['CI'];
    delete process.env['GITHUB_ACTIONS'];

    let full: string | null = null;
    try {
      full = execSync('git rev-parse HEAD', { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim();
    } catch {
      full = null;
    }
    const m = buildReportMeta();
    expect(m.agent.name.length).toBeGreaterThan(0);
    expect(m.model).toHaveProperty('name');
    expect(m.model).toHaveProperty('provider');
    expect(typeof m.iteration).toBe('number');
    if (full) expect(m.commitSha).toBe(full); else expect(m.commitSha).toBeNull();
    // branch may be null if git not available
    expect(m).toHaveProperty('branch');
    expect(typeof m.environment).toBe('string');
    expect(typeof m.createdAt).toBe('string');
  });
});

