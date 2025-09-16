import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: regression (multilingual/negation boundaries)', () => {
  it('positive phrases across languages remain OK', () => {
    const samples = [
      'Aucun contre-exemple détecté', // FR
      'Sin contraejemplos encontrados', // ES
      'Keine Gegenbeispiele gefunden' // DE
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBe(true);
  });
  it('ambiguous warnings are inconclusive (null)', () => {
    const samples = [
      'No error handlers found (info)'
    ];
    for (const s of samples) expect(computeOkFromOutput(s)).toBeNull();
  });
});
