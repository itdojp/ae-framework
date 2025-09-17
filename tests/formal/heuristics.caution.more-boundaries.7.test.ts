import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 注意:)', () => {
  it('matches JA 注意: variant', () => {
    const samples = [
      '注意: 入力を確認してください',
      '注意：仕様の前提を見直してください'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

