import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA ご案内:)', () => {
  it('matches JA ご案内:', () => {
    const s = 'ご案内: 出力の要約は参考情報です。';
    expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
  });
});

