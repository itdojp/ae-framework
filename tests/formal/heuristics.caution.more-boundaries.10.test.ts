import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 備考:)', () => {
  it('matches JA 備考: variant', () => {
    const samples = [
      '備考: 仕様の補足を確認してください',
      '備考：この結果は参考値です'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

