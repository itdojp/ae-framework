import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { makeEmail } from '../../src/lib/email';

describe('PBT: Email normalization is idempotent and case/space-insensitive', () => {
  it('makeEmail trims and lowercases; repeated make produces same value', async () => {
    const whitespace = fc.stringOf(fc.constantFrom(' ', '\t'), { maxLength: 2 });
    const casing = fc.constantFrom<'upper' | 'lower' | 'alternating'>('upper', 'lower', 'alternating');
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          email: fc.emailAddress().filter(addr => {
            const [local, rest] = addr.split('@');
            if (!local || !rest) {
              return false;
            }
            const lastDot = rest.lastIndexOf('.');
            if (lastDot <= 0 || lastDot === rest.length - 1) {
              return false;
            }
            const domain = rest.slice(0, lastDot);
            const tld = rest.slice(lastDot + 1);
            return /^[A-Za-z0-9](?:[A-Za-z0-9._+-]{0,31})$/.test(local)
              && /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,30})[A-Za-z0-9]$/.test(domain)
              && /^[A-Za-z]{2,7}$/.test(tld);
          }),
          leading: whitespace,
          trailing: whitespace,
          casing
        }),
        async ({ email, leading, trailing, casing }) => {
          let mixedCase = email;
          if (casing === 'upper') {
            mixedCase = email.toUpperCase();
          } else if (casing === 'lower') {
            mixedCase = email.toLowerCase();
          } else {
            mixedCase = email
              .split('')
              .map((char, idx) => (idx % 2 === 0 ? char.toUpperCase() : char.toLowerCase()))
              .join('');
          }
          const raw = `${leading}${mixedCase}${trailing}`;
          const e1 = makeEmail(raw) as unknown as string;
          const e2 = makeEmail(e1) as unknown as string;
          expect(e1).toBe(e2);
          expect(e1).toBe(e1.trim().toLowerCase());
        }
      ),
      { numRuns: 25 }
    );
  });
});
