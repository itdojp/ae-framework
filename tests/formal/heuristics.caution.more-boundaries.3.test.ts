import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution/notice boundaries (extra)', () => {
  it('matches EN notice and JA 注意事項', () => {
    const samples = [
      'Notice: Review required',
      '注意事項: 重要な注意点',
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

