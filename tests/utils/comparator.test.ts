import { describe, it, expect } from 'vitest';
import { compare, parseComparator, strictest } from '../../src/utils/comparator.js';

describe('comparator utils', () => {
  it('parses default operator and percent', () => {
    const parsed = parseComparator('90%');
    expect(parsed.operator).toBe('>=');
    expect(parsed.value).toBe(90);
    expect(parsed.unit).toBe('%');
    expect(parsed.baseUnit).toBe('percent');
    expect(parsed.normalizedValue).toBe(90);
  });

  it('parses time units and normalizes to ms', () => {
    const ms = parseComparator('<=200ms');
    expect(ms.operator).toBe('<=');
    expect(ms.baseUnit).toBe('ms');
    expect(ms.normalizedValue).toBe(200);

    const seconds = parseComparator('>=0.5s');
    expect(seconds.baseUnit).toBe('ms');
    expect(seconds.normalizedValue).toBe(500);
  });

  it('compares percent and ratio values', () => {
    expect(compare(0.92, '>=90%')).toBe(true);
    expect(compare(0.75, '>=90%')).toBe(false);
  });

  it('compares values with compatible units', () => {
    expect(compare('1200ms', '<=1.5s')).toBe(true);
    expect(compare('1200ms', '<1s')).toBe(false);
  });

  it('normalizes rps units', () => {
    expect(compare('120rpm', '>=2rps')).toBe(true);
  });

  it('selects strictest comparator for >= and <=', () => {
    expect(strictest('>=0.9', '>=0.85')).toBe('>=0.9');
    expect(strictest('<=200ms', '<=0.5s')).toBe('<=200ms');
  });

  it('selects equality when compatible', () => {
    expect(strictest('==0', '>=0')).toBe('==0');
  });

  it('throws on unit mismatch', () => {
    expect(() => strictest('>=90%', '<=100ms')).toThrow();
    expect(() => compare('90%', '>=0.9')).toThrow();
  });
});
