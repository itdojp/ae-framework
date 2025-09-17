import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 念のため/ご注意ください)', () => {
  it('matches JA 念のため / ご注意ください', () => {
    const samples = [
      '念のため: 実行結果は参考情報です',
      'ご注意ください: 環境差により結果が異なる可能性があります'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

