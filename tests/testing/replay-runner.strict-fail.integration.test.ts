import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { createTempDir, writeTempJson, rmrf } from '../_helpers/tmpfs.js';

describe('Integration: replay-runner (strict mode failure)', () => {
  it('exits non-zero when invariants are violated and REPLAY_STRICT=1', async () => {
    const tmpDir = createTempDir('replay-runner-');
    try {
      const events = [
        { name: 'ItemReceived', payload: { qty: 1 } },
        { name: 'ItemAllocated', payload: { qty: 2 } }
      ];
      const input = writeTempJson(tmpDir, 'events.strict.json', events);
      const output = path.join(tmpDir, 'replay.summary.strict.json');
      const res = spawnSync('node', ['scripts/testing/replay-runner.mjs'], {
        env: { ...process.env, REPLAY_INPUT: input, REPLAY_OUTPUT: output, REPLAY_STRICT: '1' },
        encoding: 'utf-8'
      });
      expect(res.status).not.toBe(0);
      expect(fs.existsSync(output)).toBe(true);
      const summary = JSON.parse(fs.readFileSync(output, 'utf-8'));
      expect(Array.isArray(summary.violatedInvariants)).toBe(true);
      expect(summary.violatedInvariants.length).toBeGreaterThan(0);
    } finally {
      rmrf(tmpDir);
    }
  });
});
