import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA 重要なお知らせ)', () => {
  it('matches JA 重要なお知らせ', () => {
    const s = '重要なお知らせ: 本実行結果は参考情報です。';
    expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
  });
});

