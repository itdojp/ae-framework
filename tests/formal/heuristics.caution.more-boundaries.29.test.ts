import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (NL Opgelet:)', () => {
  it('matches NL Opgelet:', () => {
    const samples = [
      'Opgelet: controleer de assumpties',
      'opgelet: onvolledige uitvoering'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

