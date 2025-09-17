import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Advisory:)', () => {
  it('matches EN Advisory:', () => {
    const samples = [
      'Advisory: intermediate results – increase bounds to confirm',
      'advisory: assumptions may limit completeness'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

