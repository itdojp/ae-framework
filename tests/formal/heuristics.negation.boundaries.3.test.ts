import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: additional boundaries (assertion/unsatisfied)', () => {
  it('detects explicit assertion failure / unsatisfied messages as negative', () => {
    const samples = [
      'Assertion failed at line 42',
      'Invariant unsatisfied in state S3',
      'Property unsatisfied for input a=1',
      'Spec unsatisfied under constraints',
    ];
    for (const s of samples) {
      expect(computeOkFromOutput(s)).toBe(false);
    }
  });

  it('retains null for non-decisive info lines', () => {
    const neutral = [
      'Reading model...',
      'Preparing solver context',
      'Note: using default options',
    ];
    for (const s of neutral) {
      expect(computeOkFromOutput(s)).toBeNull();
    }
  });
});

