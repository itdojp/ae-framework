import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA ご留意ください)', () => {
  it('matches JA ご留意ください', () => {
    const samples = [
      'ご留意ください: 本結果は参考情報であり、検証を完了していません',
      'ご留意ください。タイムアウトの可能性があります'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

