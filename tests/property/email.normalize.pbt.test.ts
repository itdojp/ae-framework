import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { z } from 'zod';
import { makeEmail } from '../../src/lib/email';

describe('PBT: makeEmail normalization', () => {
  it('trimsとlowercaseを行い妥当なメールを生成する', async () => {
    const emailSchema = z.string().email();
    const arbEmail = fc
      .emailAddress()
      .map((email) => {
        // 正常化の挙動を検証するため、大文字＋前後空白を付与
        const upper = email.toUpperCase();
        return {
          raw: `  ${upper}  `,
          expected: upper.trim().toLowerCase(),
        };
      })
      .filter(({ expected }) => emailSchema.safeParse(expected).success);

    await fc.assert(
      fc.asyncProperty(arbEmail, async ({ raw, expected }) => {
        const res = makeEmail(raw) as unknown as string;
        expect(res).toBe(expected);
      }),
      { numRuns: 50 }
    );
  });

  it('@ を含まない文字列は拒否する', async () => {
    const arbInvalid = fc
      .string({ minLength: 1, maxLength: 32 })
      .filter((s) => !s.includes('@') && s.trim().length > 0);

    await fc.assert(
      fc.asyncProperty(arbInvalid, async (candidate) => {
        let ok = true;
        try {
          makeEmail(candidate);
        } catch {
          ok = false;
        }
        expect(ok).toBe(false);
      }),
      { numRuns: 30 }
    );
  });
});
