import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 重要:)', () => {
  it('matches JA 重要: variant', () => {
    const samples = [
      '重要: 仕様の前提を確認してください',
      '重要：この結果は警告を含みます'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

