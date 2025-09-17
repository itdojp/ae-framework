import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: additional multilingual positives', () => {
  it('accepts common positive phrases across FR/ES/DE', () => {
    const samples = [
      'Aucune violation détectée', // FR
      'No se detectaron errores', // ES variant
      'Keine Fehler gefunden' // DE
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBe(true);
  });
});

