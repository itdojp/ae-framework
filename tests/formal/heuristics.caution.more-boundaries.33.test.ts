import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA ご承知おきください)', () => {
  it('matches JA ご承知おきください', () => {
    const samples = [
      'ご承知おきください: これは注意喚起であり、失敗の確定ではありません',
      'ご承知おきください。実行条件に制約があります'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

