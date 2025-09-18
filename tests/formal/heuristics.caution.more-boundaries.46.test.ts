import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: CAUTION boundaries (46)', () => {
  it('matches polite Japanese caution requests', () => {
    const samples = [
      'ご注意のほどお願いします: 入力サイズにご留意ください。',
      'ご注意のほどお願いいたします：ログの取り扱い'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some(re => re.test(s))).toBe(true);
    }
  });
});

