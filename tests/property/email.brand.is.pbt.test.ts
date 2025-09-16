import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { Email, makeEmail } from '../../src/lib/email';

describe('PBT: Email brand is() and make()', () => {
  it('is() returns true for values produced by make()', async () => {
    const localChars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._%+-';
    const arbLocal = fc.stringOf(fc.constantFrom(...localChars.split('')), { minLength: 1, maxLength: 10 });
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

