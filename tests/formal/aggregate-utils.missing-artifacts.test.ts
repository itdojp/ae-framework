import { describe, it, expect } from 'vitest';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { computeAggregateInfo } from '../../scripts/formal/aggregate-utils.mjs';

describe('Formal aggregate utils: missing/invalid artifacts safety', () => {
  it('returns present=false when summary files are absent', () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'agg-')); 
    const info = computeAggregateInfo(tmp);
    expect(info.present).toEqual({ tla: false, alloy: false, smt: false, apalache: false, conformance: false });
    expect(info.presentCount).toBe(0);
    expect(info.ranOk.apalache).toBeNull();
  });
  it('handles invalid JSON gracefully (present=true but ranOk null)', () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'agg-'));
    const p = path.join(tmp, 'formal-reports-apalache');
    fs.mkdirSync(p, { recursive: true });
    fs.writeFileSync(path.join(p, 'apalache-summary.json'), '{invalid json');
    const info = computeAggregateInfo(tmp);
    expect(info.present.apalache).toBe(true);
    expect(info.ranOk.apalache).toBeNull();
  });
  it('extracts ran/ok from apalache summary if present', () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'agg-'));
    const p = path.join(tmp, 'formal-reports-apalache');
    fs.mkdirSync(p, { recursive: true });
    fs.writeFileSync(path.join(p, 'apalache-summary.json'), JSON.stringify({ ran: false, ok: null }));
    const info = computeAggregateInfo(tmp);
    expect(info.present.apalache).toBe(true);
    expect(info.ranOk.apalache).toEqual({ ran: false, ok: null });
  });
});

