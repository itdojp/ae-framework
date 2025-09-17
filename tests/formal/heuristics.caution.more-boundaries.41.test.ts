import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Be advised:)', () => {
  it('matches EN Be advised:', () => {
    const samples = [
      'Be advised: results may be partial',
      'be advised: adjust bounds to explore more'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

