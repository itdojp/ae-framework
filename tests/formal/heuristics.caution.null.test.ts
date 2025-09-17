import { describe, it, expect } from 'vitest';
import { computeOkFromOutput } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution/warning phrases remain inconclusive', () => {
  it('returns null for cautionary notes without explicit failure/ok', () => {
    const notes = [
      'Analysis completed with warnings only',
      'Some checks were skipped due to configuration',
      'Avertissement: résultats partiels', // FR
      'Advertencia: resultados parciales',  // ES
      'Hinweis: Teilresultate'              // DE
    ];
    for (const s of notes) expect(computeOkFromOutput(s)).toBeNull();
  });
});

