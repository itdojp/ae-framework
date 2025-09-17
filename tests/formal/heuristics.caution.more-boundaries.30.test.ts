import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Heads-up:)', () => {
  it('matches EN Heads-up:', () => {
    const samples = [
      'Heads-up: partial exploration; results may be incomplete',
      'heads-up: verify assumptions and rerun with higher bounds'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

