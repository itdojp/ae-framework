import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';

describe('Integration: replay-runner (strict mode failure)', () => {
  it('exits non-zero when invariants are violated and REPLAY_STRICT=1', async () => {
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'replay-runner-'));
    const input = path.join(tmpDir, 'events.strict.json');
    const output = path.join(tmpDir, 'replay.summary.strict.json');
    // Create a violation: allocate more than onHand
    const events = [
      { name: 'ItemReceived', payload: { qty: 1 } },
      { name: 'ItemAllocated', payload: { qty: 2 } }
    ];
    fs.writeFileSync(input, JSON.stringify(events, null, 2));
    const res = spawnSync('node', ['scripts/testing/replay-runner.mjs'], {
      env: { ...process.env, REPLAY_INPUT: input, REPLAY_OUTPUT: output, REPLAY_STRICT: '1' },
      encoding: 'utf-8'
    });
    expect(res.status).not.toBe(0);
    expect(fs.existsSync(output)).toBe(true);
    const summary = JSON.parse(fs.readFileSync(output, 'utf-8'));
    expect(Array.isArray(summary.violatedInvariants)).toBe(true);
    expect(summary.violatedInvariants.length).toBeGreaterThan(0);
  });
});

