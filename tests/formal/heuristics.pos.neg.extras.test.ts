import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: extra positive/negative patterns', () => {
  it('accepts additional positive messages', () => {
    const pos = [
      'All invariants satisfied',
      'No property violations',
      'No counterexample found in 12 steps'
    ];
    for (const s of pos) expect(computeOkFromOutput(s)).toBe(true);
  });
  it('detects additional negative messages', () => {
    const neg = [
      'Invariant violated at state 3',
      'Propriété violée',
      'Propiedad violada'
    ];
    for (const s of neg) expect(computeOkFromOutput(s)).toBe(false);
  });
});

