import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';

const generatorScript = resolve('scripts/formal/generate-formal-summary-v1.mjs');

function writeJson(p: string, data: unknown) {
  mkdirSync(dirname(p), { recursive: true });
  writeFileSync(p, JSON.stringify(data, null, 2), 'utf8');
}

function runNode(cwd: string, args: string[], env: Record<string, string>) {
  return spawnSync('node', [generatorScript, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env },
  });
}

describe('formal-summary/v1 generator', () => {
  it('supports hermetic layout inputs', () => {
    const dir = mkdtempSync(join(tmpdir(), 'formal-summary-v1-'));
    try {
      const commit = '0123456789abcdef0123456789abcdef01234567';

      writeJson(join(dir, 'input', 'formal', 'tla-summary.json'), { ran: true, status: 'ran' });
      writeJson(join(dir, 'input', 'formal', 'alloy-summary.json'), { ok: true, exitCode: 0, timeMs: 10 });
      writeJson(join(dir, 'input', 'conformance', 'summary.json'), { ok: true, exitCode: 0, timeMs: 5 });

      const out = join(dir, 'out', 'formal-summary-v1.json');
      const result = runNode(dir, ['--layout', 'hermetic', '--in', 'input', '--out', out], { GIT_COMMIT: commit });
      expect(result.status).toBe(0);

      const payload = JSON.parse(readFileSync(out, 'utf8'));
      expect(payload.schemaVersion).toBe('formal-summary/v1');
      expect(payload.tool).toBe('aggregate');
      expect(payload.metadata.gitCommit).toBe(commit);

      const names = payload.results.map((r: any) => r.name);
      expect(names).toEqual(['tla', 'alloy', 'smt', 'apalache', 'conformance', 'kani', 'spin', 'csp', 'lean']);

      const byName = Object.fromEntries(payload.results.map((r: any) => [r.name, r]));
      expect(byName.alloy.status).toBe('ok');
      expect(byName.alloy.code).toBe(0);
      expect(byName.alloy.durationMs).toBe(10);

      expect(byName.conformance.status).toBe('ok');
      expect(byName.conformance.code).toBe(0);
      expect(byName.conformance.durationMs).toBe(5);

      // ran without ok flag is normalized to unknown (fact-only)
      expect(byName.tla.status).toBe('unknown');
      expect(byName.tla.reason).toBe('ran_without_ok');

      // missing inputs still get an explicit result entry
      expect(byName.smt.status).toBe('missing');
      expect(byName.apalache.status).toBe('missing');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});

