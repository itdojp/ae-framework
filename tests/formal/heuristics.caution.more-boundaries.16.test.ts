import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN NB: / N.B.:)', () => {
  it('matches EN NB: / N.B.:', () => {
    const samples = [
      'NB: check assumptions',
      'N.B.: results are indicative'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

