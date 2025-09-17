import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (ES Advertencia:)', () => {
  it('matches ES Advertencia:', () => {
    const samples = [
      'Advertencia: revise los supuestos',
      'advertencia: exploración parcial'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

