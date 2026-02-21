import { describe, expect, test } from 'vitest';
import { InputSchema, OutputSchema } from '../../src/contracts/schemas.js';

describe('contracts fallback schemas', () => {
  test('InputSchema accepts arbitrary values', () => {
    expect(InputSchema.parse('text')).toBe('text');
    expect(InputSchema.parse({ key: 'value' })).toEqual({ key: 'value' });
    expect(InputSchema.parse([1, 2, 3])).toEqual([1, 2, 3]);
  });

  test('OutputSchema accepts arbitrary values', () => {
    expect(OutputSchema.parse(null)).toBeNull();
    expect(OutputSchema.parse({ ok: true })).toEqual({ ok: true });
    expect(OutputSchema.parse(42)).toBe(42);
  });
});
