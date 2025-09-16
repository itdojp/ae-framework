import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: negation/warning boundaries', () => {
  it('negative/violation words are detected as NG', () => {
    const samples = [
      'Violation detected at step 3',
      'Counterexample found',
      'Deadlock detected'
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBe(false);
  });
  it('informational warnings remain inconclusive', () => {
    const samples = [
      'Tool ran with warnings (informational)',
      'No error handlers found (info)'
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBeNull();
  });
});

