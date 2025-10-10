import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { Email, makeEmail } from '../../src/lib/email';

describe('PBT: Email brand is() and make()', () => {
  it('is() returns true for values produced by make()', async () => {
    const headChars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';
    const tailChars = headChars + '._+-';
    const arbLocal = fc.tuple(
      fc.constantFrom(...headChars.split('')),
      fc.stringOf(fc.constantFrom(...tailChars.split('')), { maxLength: 9 })
    ).map(([head, tail]) => {
      const sanitizedTail = tail.replace(/[._+-]+$/g, '');
      return `${head}${sanitizedTail}`;
    });
    await fc.assert(fc.asyncProperty(
      arbLocal,
      async (local) => {
        const raw = `${local}@Example.COM`;
        const e = makeEmail(raw);
        expect(Email.is(e)).toBe(true);
      }
    ), { numRuns: 30 });
  });
});
