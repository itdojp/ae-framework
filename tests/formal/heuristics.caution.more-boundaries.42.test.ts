import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 周知)', () => {
  it('matches JA 周知', () => {
    const samples = [
      '周知: 本結果は参考情報です',
      '周知: 追加検証が必要です'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

