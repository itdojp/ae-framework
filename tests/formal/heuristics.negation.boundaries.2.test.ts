import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: additional negation/caution boundaries', () => {
  it('detects clear negatives across EN/ES/DE/FR', () => {
    const samples = [
      'Counterexample produced at step 12',
      'The property does not hold for this execution',
      'La propiedad no se cumple en este estado',
      'Die Eigenschaft gilt nicht unter diesen Bedingungen',
      'La propriété ne tient pas pour ce cas',
    ];
    for (const s of samples) {
      expect(computeOkFromOutput(s)).toBe(false);
    }
  });

  it('keeps null for non‑decisive messages', () => {
    const neutral = [
      'Analysis started...',
      'Parsing input files',
      'Checking invariants (this may take a while)',
    ];
    for (const s of neutral) {
      expect(computeOkFromOutput(s)).toBeNull();
    }
  });

  it('does not regress positives', () => {
    const positives = [
      'No counterexample found in 100 steps',
      'Verification successful: all invariants hold',
      'Keine Fehler gefunden',
      'Aucune violation détectée',
    ];
    for (const s of positives) {
      expect(computeOkFromOutput(s)).toBe(true);
    }
  });
});

