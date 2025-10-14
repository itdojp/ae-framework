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
      const sanitizedTail = tail
        .replace(/[._+-]+$/g, '')
        .replace(/[^a-zA-Z0-9._+-]/g, '')
        .replace(/\.+/g, '.')
        .replace(/[._+-]{2,}/g, (match) => match[0]);
      const remainder = sanitizedTail.length > 0 ? sanitizedTail : '0';
      const local = `${head}${remainder}`
        .replace(/\.+/g, '.')
        .replace(/[._+-]{2,}/g, (match) => match[0]);
      return local.replace(/\.$/, '');
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
