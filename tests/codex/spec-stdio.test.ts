import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';

const scriptPath = resolve('scripts/codex/spec-stdio.mjs');

const runBridge = (payload: Record<string, unknown>) => {
  return spawnSync(process.execPath, [scriptPath], {
    input: `${JSON.stringify(payload)}\n`,
    encoding: 'utf8',
    timeout: 60_000,
  });
};

const parseLastJsonLine = (stdout: string) => {
  const line = stdout.trim().split('\n').filter(Boolean).pop() || '{}';
  return JSON.parse(line);
};

describe('spec-stdio bridge', () => {
  it('works in direct execution path for validate', () => {
    const result = runBridge({
      action: 'validate',
      args: {
        inputPath: 'spec/0_first_valid_spec.md',
        relaxed: true,
        maxWarnings: 200,
      },
    });
    expect(result.status).toBe(0);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(true);
    expect(parsed.data?.summary).toBeDefined();
  });

  it('returns non-zero on unknown action', () => {
    const result = runBridge({ action: 'unknown-action' });
    expect(result.status).toBe(2);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('Unknown action');
  });

  it('returns non-zero on missing action', () => {
    const result = runBridge({ args: {} });
    expect(result.status).toBe(2);
    const parsed = parseLastJsonLine(result.stdout);
    expect(parsed.ok).toBe(false);
    expect(parsed.error).toContain('Missing action');
  });
});
