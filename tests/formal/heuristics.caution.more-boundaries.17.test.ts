import { describe, it, expect } from 'vitest';
import { CAUTION_PATTERNS } from '../../scripts/formal/heuristics.mjs';

describe('Formal heuristics: caution boundaries (DE Hinweis:)', () => {
  it('matches DE Hinweis:', () => {
    const samples = [
      'Hinweis: unvollständige Prüfung',
      'hinweis: bitte Voraussetzungen prüfen'
    ];
    for (const s of samples) {
      expect(CAUTION_PATTERNS.some((re) => re.test(s))).toBe(true);
    }
  });
});

