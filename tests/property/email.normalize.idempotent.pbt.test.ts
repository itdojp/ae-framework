import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { z } from 'zod';
import { makeEmail } from '../../src/lib/email';

describe('PBT: Email normalization is idempotent and case/space-insensitive', () => {
  it('makeEmail trimsとlowercaseを行い、再度makeしても変化しない', async () => {
    const emailSchema = z.string().email();
    const arbEmail = fc
      .emailAddress()
      .map((email) => {
        const upper = email.toUpperCase();
        return {
          raw: `  ${upper}  `,
          expected: upper.trim().toLowerCase(),
        };
      })
      .filter(({ expected }) => emailSchema.safeParse(expected).success);

    await fc.assert(
      fc.asyncProperty(arbEmail, async ({ raw, expected }) => {
        const first = makeEmail(raw) as unknown as string;
        const second = makeEmail(first) as unknown as string;
        expect(first).toBe(expected);
        expect(second).toBe(expected);
      }),
      { numRuns: 30 }
    );
  });
});
