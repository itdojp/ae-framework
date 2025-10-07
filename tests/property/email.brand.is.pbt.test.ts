import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { z } from 'zod';
import { Email, makeEmail } from '../../src/lib/email';

describe('PBT: Email brand is() and make()', () => {
  it('is() returns true for values produced by make()', async () => {
    const emailSchema = z.string().email();
    const arbEmail = fc
      .emailAddress()
      .map((email) => email.toUpperCase())
      .filter((candidate) => emailSchema.safeParse(candidate.toLowerCase()).success);

    await fc.assert(
      fc.asyncProperty(arbEmail, async (raw) => {
        const value = makeEmail(raw);
        expect(Email.is(value)).toBe(true);
      }),
      { numRuns: 30 }
    );
  });
});
