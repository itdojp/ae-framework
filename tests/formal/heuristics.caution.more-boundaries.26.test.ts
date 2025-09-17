import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (IT Attenzione:)', () => {
  it('matches IT Attenzione:', () => {
    const samples = [
      'Attenzione: verificare le ipotesi',
      'attenzione: esplorazione parziale'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

