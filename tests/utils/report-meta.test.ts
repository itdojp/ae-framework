import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { getCommonMeta } from '../../src/utils/report-meta.js';
import { execSync } from 'node:child_process';

const ENV_SNAPSHOT: NodeJS.ProcessEnv = { ...process.env };

describe('getCommonMeta', () => {
  beforeEach(() => {
    process.env = { ...ENV_SNAPSHOT };
  });
  afterEach(() => {
    process.env = { ...ENV_SNAPSHOT };
  });

  it('returns env-provided fields when present (shape with nested agent/model)', () => {
    process.env['AE_AGENT'] = 'test-agent';
    process.env['AE_AGENT_VERSION'] = '0.9.9-test';
    process.env['OPENAI_MODEL'] = 'gpt-x';
    process.env['TRACE_ID'] = 'trace-123';
    process.env['GITHUB_RUN_ID'] = '99999';
    process.env['GITHUB_SHA'] = 'abcdef0123456789abcdef0123456789abcdef01';
    process.env['GITHUB_REF_NAME'] = 'feat/test';

    const meta = getCommonMeta();
    expect(meta.agent.name).toBe('test-agent');
    expect(meta.agent.version).toBe('0.9.9-test');
    expect(meta.model?.name).toBe('gpt-x');
    expect(meta.model?.provider).toBe('openai');
    expect(meta.traceId).toBe('trace-123');
    expect(meta.runId).toBe('99999');
    expect(meta.commitSha).toBe('abcdef0123456789abcdef0123456789abcdef01');
    expect(meta.branch).toBe('feat/test');
    expect(typeof meta.createdAt).toBe('string');
    expect(typeof meta.environment).toBe('string');
  });

  it('falls back to git full commit when CI vars missing', () => {
    delete process.env['GITHUB_SHA'];
    delete process.env['CI_COMMIT_SHA'];
    delete process.env['GIT_COMMIT'];

    let full: string | null = null;
    try {
      full = execSync('git rev-parse HEAD', { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim();
    } catch {
      full = null;
    }
    const meta = getCommonMeta();
    if (full) {
      expect(meta.commitSha).toBe(full);
    } else {
      expect(meta.commitSha).toBeNull();
    }
  });
});
