import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (EN Notice to readers:)', () => {
  it('matches EN Notice to readers:', () => {
    const s = 'Notice to readers: This is an advisory.';
    expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
  });
});

