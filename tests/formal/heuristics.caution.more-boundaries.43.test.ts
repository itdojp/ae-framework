import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Please be advised:)', () => {
  it('matches EN Please be advised:', () => {
    const samples = [
      'Please be advised: partial results',
      'please be advised: check assumptions'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

