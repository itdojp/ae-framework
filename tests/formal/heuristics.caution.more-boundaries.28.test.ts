import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (NL Let op:)', () => {
  it('matches NL Let op:', () => {
    const samples = [
      'Let op: controleer de aannames',
      'let op: gedeeltelijke verkenning'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

