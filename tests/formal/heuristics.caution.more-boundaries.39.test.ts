import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 参考情報)', () => {
  it('matches JA 参考情報', () => {
    const samples = [
      '参考情報: 本結果は概要のみを示します',
      '参考情報: 成否判定ではありません'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

