import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (ES Nota:)', () => {
  it('matches ES Nota:', () => {
    const samples = [
      'Nota: revise los invariantes',
      'nota: verifique los supuestos'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

