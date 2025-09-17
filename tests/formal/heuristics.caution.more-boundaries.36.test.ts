import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN FYI:)', () => {
  it('matches EN FYI:', () => {
    const samples = [
      'FYI: partial check only',
      'fyi: run with higher bounds for completeness'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

