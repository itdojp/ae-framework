import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (DE Warnung:)', () => {
  it('matches DE Warnung:', () => {
    const samples = [
      'Warnung: unvollständige Prüfung',
      'warnung: bitte Voraussetzungen prüfen'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

