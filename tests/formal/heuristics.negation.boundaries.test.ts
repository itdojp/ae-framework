import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: negation/caution boundaries (multilingual)', () => {
  it('treats cautionary mentions of "counterexample" without found/detected as inconclusive', () => {
    const samples = [
      'Could not reproduce counterexample in this run',
      'Counterexample reproduction not available',
      'No se pudo reproducir el contraejemplo',
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBeNull();
  });
  it('recognizes additional positive phrases', () => {
    const samples = [
      'No errors found',
      'No se encontraron errores',
      'Aucun échec détecté',
      'Keine Verletzungen gefunden'
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBe(true);
  });
});

