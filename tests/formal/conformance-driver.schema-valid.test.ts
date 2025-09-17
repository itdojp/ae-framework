import { describe, it, expect } from 'vitest';
import { execSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

describe('Formal: conformance-driver emits schema-conformant summary', () => {
  it('writes conformance-summary.json with required ran/ok fields', () => {
    const out = 'hermetic-reports/formal/conformance-summary.json';
    // prepare minimal replay summary
    const replay = {
      traceId: 't-1',
      totalEvents: 3,
      violatedInvariants: []
    };
    fs.mkdirSync(path.dirname('artifacts/domain/replay.summary.json'), { recursive: true });
    fs.writeFileSync('artifacts/domain/replay.summary.json', JSON.stringify(replay));

    // run driver
    execSync('node scripts/formal/conformance-driver.mjs', { stdio: 'inherit' });
    expect(fs.existsSync(out)).toBe(true);

    const j = JSON.parse(fs.readFileSync(out, 'utf-8'));
    // schema-required
    expect(typeof j.ran).toBe('boolean');
    expect(j.ok === true || j.ok === false || j.ok === null).toBe(true);
    // helpful fields
    expect(j.tool).toBe('conformance-driver');
  });
});

