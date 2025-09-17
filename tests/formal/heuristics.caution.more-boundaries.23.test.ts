import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (JA ご注意)', () => {
  it('matches JA ご注意', () => {
    const samples = [
      'ご注意: 仕様の注意点を確認してください',
      'ご注意 この検査は参考値です'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

