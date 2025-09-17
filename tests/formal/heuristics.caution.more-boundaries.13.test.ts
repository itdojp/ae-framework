import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 補足:)', () => {
  it('matches JA 補足: variant', () => {
    const samples = [
      '補足: 参考情報です',
      '補足：検査範囲を確認してください'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

