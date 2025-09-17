import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Reminder:)', () => {
  it('matches EN Reminder:', () => {
    const samples = [
      'Reminder: this is an informational note',
      'reminder: results may be partial'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

