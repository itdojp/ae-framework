import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics — CAUTION boundaries (+1)', () => {
  it('matches EN "Heads up:" and JA 「ご留意ください」', () => {
    const samples = [
      'Heads up: this is a cautionary note.',
      'ご留意ください: 重要な注意事項があります。'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

