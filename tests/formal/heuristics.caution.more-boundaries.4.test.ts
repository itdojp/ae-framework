import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (heads up / 注意喚起)', () => {
  it('matches EN heads up and JA 注意喚起', () => {
    const samples = [
      'Heads up: limited run',
      '注意喚起: 出力の要確認',
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

