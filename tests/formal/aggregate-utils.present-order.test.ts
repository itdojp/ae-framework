import { describe, it, expect } from 'vitest';
import { ORDERED_PRESENT_KEYS, orderedPresentPairs, formatByTypePresentLine } from '../../scripts/formal/aggregate-utils.mjs';

describe('Formal aggregate utils: ordered present pairs and MD line', () => {
  it('returns keys in deterministic order', () => {
    expect(ORDERED_PRESENT_KEYS).toEqual(['tla','alloy','smt','apalache','conformance']);
    const present = { smt: true, conformance: true, tla: true, alloy: false, apalache: true };
    const pairs = orderedPresentPairs(present);
    expect(pairs.map(([k]) => k)).toEqual(['tla','smt','apalache','conformance']);
  });

  it('formats MD line with count and names (non-empty)', () => {
    const info = { present: { tla: true, alloy: true, smt: false, apalache: true, conformance: false } };
    const line = formatByTypePresentLine(info);
    expect(line).toBe('By-type present: 3/5 (tla, alloy, apalache)');
  });

  it('formats MD line for empty case', () => {
    const line = formatByTypePresentLine({ present: { tla: false, alloy: false, smt: false, apalache: false, conformance: false } });
    expect(line).toBe('By-type present: 0/5');
  });
});

