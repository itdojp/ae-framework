import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN For your reference:)', () => {
  it('matches EN For your reference:', () => {
    const samples = [
      'For your reference: intermediate results only',
      'for your reference: re-run with extended bounds'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

