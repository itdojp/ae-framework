import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 警告:)', () => {
  it('matches JA 警告: variant', () => {
    const samples = [
      '警告: 結果は参考です',
      '警告：前提条件を確認してください'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

