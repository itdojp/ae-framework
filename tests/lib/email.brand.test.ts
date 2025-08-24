import { test, expect } from 'vitest';
import { makeEmail } from '../../src/lib/email';

test('makeEmail normalizes and validates', () => {
  expect(makeEmail('  Foo@Example.com ')).toBe('foo@example.com' as any);
  expect(() => makeEmail('invalid')).toThrow();
});