import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: additional caution boundaries', () => {
  it('matches multilingual caution/attention phrases conservatively', () => {
    const samples = [
      'Attention: review incomplete traces',
      'Achtung: Ergebnis könnte unvollständig sein',
      'Precaución: verifique los invariantes',
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

