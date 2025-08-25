import { test, expect } from 'vitest';
import { makeEmail, Email } from '../../src/lib/email';

test('makeEmail normalizes and validates', () => {
  expect(makeEmail('  Foo@Example.com ')).toBe('foo@example.com' as Email);
  expect(() => makeEmail('invalid')).toThrow();
});