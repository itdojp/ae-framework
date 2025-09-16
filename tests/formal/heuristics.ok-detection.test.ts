import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: computeOkFromOutput', () => {
  it('detects positive outputs', () => {
    const samples = [
      'No counterexamples found. Verification successful.',
      'OK: all properties hold',
      'Invariant holds and no violations',
      'Aucun contre-exemple trouvé',
      'Sin contraejemplos',
      'Keine Gegenbeispiele'
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBe(true);
  });
  it('detects negative outputs', () => {
    const samples = [
      'Error: violation detected',
      'Counterexample found at step 12',
      'Failed to prove property'
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBe(false);
  });
  it('returns null on inconclusive outputs', () => {
    expect(computeOkFromOutput('Tool ran with warnings')).toBeNull();
    // Negative false-positive guard: contains the word "error" but not actual failure semantics
    expect(computeOkFromOutput('no error handlers found')).toBeNull();
    expect(computeOkFromOutput('no failures detected but warnings present')).toBeNull();
  });
});
