import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (ES Cuidado:)', () => {
  it('matches ES Cuidado:', () => {
    const samples = [
      'Cuidado: verifique los supuestos',
      'cuidado: ejecución parcial'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

