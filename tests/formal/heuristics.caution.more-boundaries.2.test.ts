import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA/ES extra)', () => {
  it('matches JA/ES attention-like phrases', () => {
    const samples = [
      '注意: この結果は要確認',
      'Aviso: revise los resultados',
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

