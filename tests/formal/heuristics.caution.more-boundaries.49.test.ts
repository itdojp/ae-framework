import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 注意喚起です:)', () => {
  it('matches JA 注意喚起です:', () => {
    const s = '注意喚起です: 出力は参考情報です。';
    expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
  });
});

