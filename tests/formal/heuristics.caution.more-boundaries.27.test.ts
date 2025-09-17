import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (PT Atenção:)', () => {
  it('matches PT Atenção:', () => {
    const samples = [
      'Atenção: verifique as suposições',
      'atenção: exploração parcial'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

