import { describe, it, expect } from 'vitest';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { computeAggregateInfo } from '../../scripts/formal/aggregate-utils.mjs';

describe('Formal aggregate utils: presentCount reflects available summaries', () => {
  it('counts present summaries among tla/alloy/smt/apalache/conformance', () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'agg-'));
    const mk = (p: string) => { fs.mkdirSync(path.dirname(p), { recursive: true }); fs.writeFileSync(p, '{}'); };
    mk(path.join(tmp, 'formal-reports-tla/tla-summary.json'));
    mk(path.join(tmp, 'formal-reports-alloy/alloy-summary.json'));
    // omit smt
    mk(path.join(tmp, 'formal-reports-apalache/apalache-summary.json'));
    // omit conformance
    const info = computeAggregateInfo(tmp);
    expect(info.present).toEqual({ tla: true, alloy: true, smt: false, apalache: true, conformance: false });
    expect(info.presentCount).toBe(3);
  });
});

