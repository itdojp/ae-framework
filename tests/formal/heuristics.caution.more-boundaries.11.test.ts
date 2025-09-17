import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Caveat:)', () => {
  it('matches EN Caveat:', () => {
    const samples = [
      'Caveat: partial exploration only',
      'caveat: properties may be incomplete'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

