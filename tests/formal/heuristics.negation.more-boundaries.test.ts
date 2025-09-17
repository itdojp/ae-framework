import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: additional FR/ES/DE negative boundaries', () => {
  it('detects explicit failure/violation mentions', () => {
    const negatives = [
      'Échec détecté lors de la vérification',
      'Violación detectada en el paso 10',
      'Fehler gefunden in Zustandsgraph'
    ];
    for (const s of negatives) expect(computeOkFromOutput(s)).toBe(false);
  });
  it('keeps cautionary/warning notes inconclusive (null)', () => {
    const notes = [
      'Analysis completed with warnings',
      'Avertissement: certaines vérifications ont été ignorées',
      'Advertencia: resultados parciales'
    ];
    for (const s of notes) expect(computeOkFromOutput(s)).toBeNull();
  });
});

