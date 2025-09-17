import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 注意点)', () => {
  it('matches JA 注意点', () => {
    const samples = [
      '注意点: 事前条件を見直してください',
      'この検査には注意点があります'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

