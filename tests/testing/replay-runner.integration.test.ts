import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

describe('Integration: replay-runner', () => {
  it('produces a summary JSON with expected keys', async () => {
    const tmpDir = path.join(process.cwd(), 'artifacts', 'domain');
    fs.mkdirSync(tmpDir, { recursive: true });
    const input = path.join(tmpDir, 'events.sample.json');
    const output = path.join(tmpDir, 'replay.summary.sample.json');
    const events = [
      { name: 'ItemReceived', payload: { qty: 2 } },
      { name: 'ItemAllocated', payload: { qty: 1 } },
      { name: 'ItemShipped', payload: { qty: 1 } }
    ];
    fs.writeFileSync(input, JSON.stringify(events, null, 2));
    const res = spawnSync('node', ['scripts/testing/replay-runner.mjs'], {
      env: { ...process.env, REPLAY_INPUT: input, REPLAY_OUTPUT: output, REPLAY_STRICT: '0' },
      encoding: 'utf-8'
    });
    expect(res.status).toBe(0);
    expect(fs.existsSync(output)).toBe(true);
    const summary = JSON.parse(fs.readFileSync(output, 'utf-8'));
    expect(summary).toHaveProperty('traceId');
    expect(summary).toHaveProperty('totalEvents', events.length);
    expect(summary).toHaveProperty('finalState');
    expect(summary).toHaveProperty('violatedInvariants');
  });
});

