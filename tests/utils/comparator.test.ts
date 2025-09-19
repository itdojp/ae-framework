import { describe, it, expect } from 'vitest';
import { parseComparator, compare, strictest } from '../../src/utils/comparator.js';

describe('utils/comparator', () => {
  describe('parseComparator', () => {
    it('parses percentage and normalizes to ratio', () => {
      const c = parseComparator('>= 90%');
      expect(c).toEqual({ op: '>=', value: 0.9, unit: undefined });
    });

    it('parses time and normalizes to ms', () => {
      const gt = parseComparator('>1s');
      expect(gt).toEqual({ op: '>', value: 1000, unit: 'ms' });

      const le = parseComparator('<= 500ms');
      expect(le).toEqual({ op: '<=', value: 500, unit: 'ms' });
    });

    it('parses rps unit', () => {
      const eq = parseComparator('== 200 rps');
      expect(eq).toEqual({ op: '==', value: 200, unit: 'rps' });
    });
  });

  describe('compare', () => {
    it('compares ratio against percentage expression', () => {
      expect(compare(0.95, '>= 90%')).toBe(true);
      expect(compare(0.89, '>= 90%')).toBe(false);
    });

    it('compares percentage actual string against numeric expression', () => {
      expect(compare('95%', '>= 0.9')).toBe(true);
      expect(compare('80%', '>= 0.9')).toBe(false);
    });

    it('compares time across mixed units', () => {
      expect(compare('950ms', '< 1s')).toBe(true);
      expect(compare({ value: 1, unit: 's' }, '<= 1000ms')).toBe(true);
      expect(compare({ value: 2, unit: 's' }, '<= 1500ms')).toBe(false);
    });

    it('compares rps unit', () => {
      expect(compare({ value: 120, unit: 'rps' }, '>= 100 rps')).toBe(true);
      expect(compare(80, '>= 100 rps')).toBe(false);
    });
  });

  describe('strictest', () => {
    it('returns stricter for greater-direction comparators', () => {
      expect(strictest('>= 90%', '>= 95%')).toBe('>= 95%');
      expect(strictest('> 10 rps', '>= 10 rps')).toBe('> 10 rps');
    });

    it('returns stricter for less-direction comparators', () => {
      expect(strictest('< 500ms', '<= 1s')).toBe('< 500ms');
      expect(strictest('<= 400ms', '<= 1s')).toBe('<= 400ms');
    });
  });
});

