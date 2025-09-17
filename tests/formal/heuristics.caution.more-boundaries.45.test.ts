import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Important:, JA 留意事項)', () => {
  it('matches EN Important:', () => {
    const s = 'Important: the following results are for reference only.';
    expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
  });

  it('matches JA 留意事項', () => {
    const s = '留意事項: 実行ログは参考情報としてご確認ください。';
    expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
  });
});

