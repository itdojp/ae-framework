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

  it('returns env-provided fields when present', () => {
    process.env['AE_AGENT'] = 'test-agent';
    process.env['OPENAI_MODEL'] = 'gpt-x';
    process.env['TRACE_ID'] = 'trace-123';
    process.env['GITHUB_RUN_ID'] = '99999';
    process.env['GITHUB_SHA'] = 'abcdef0123456789';

    const meta = getCommonMeta();
    expect(meta.agent).toBe('test-agent');
    expect(meta.model).toBe('gpt-x');
    expect(meta.traceId).toBe('trace-123');
    expect(meta.runId).toBe('99999');
    expect(meta.commit).toBe('abcdef0');
  });

  it('falls back to git short commit when CI vars missing', () => {
    delete process.env['GITHUB_SHA'];
    delete process.env['CI_COMMIT_SHA'];
    delete process.env['GIT_COMMIT'];

    let short: string | null = null;
    try {
      short = execSync('git rev-parse --short HEAD', { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim();
    } catch {
      short = null;
    }
    const meta = getCommonMeta();
    if (short) {
      expect(meta.commit).toBe(short);
    } else {
      expect(meta.commit).toBeNull();
    }
  });
});

