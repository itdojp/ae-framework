import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (FR Veuillez noter:)', () => {
  it('matches FR Veuillez noter:', () => {
    const samples = [
      'Veuillez noter: ces résultats sont partiels',
      'veuillez noter: vérifiez les hypothèses avant de conclure'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

