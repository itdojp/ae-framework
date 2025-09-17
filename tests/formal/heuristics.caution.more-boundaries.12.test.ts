import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 留意点)', () => {
  it('matches JA 留意点', () => {
    const samples = [
      '留意点: 仕様の前提条件を見直してください',
      'この検査結果には留意点があります'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

