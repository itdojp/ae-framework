import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { makeEmail } from '../../src/lib/email';

describe('PBT: Email normalization is idempotent and case/space-insensitive', () => {
  it('makeEmail trims and lowercases; repeated make produces same value', async () => {
    await fc.assert(fc.asyncProperty(
      fc.tuple(fc.string(), fc.string(), fc.string()).filter(([l, d, t]) => {
        // crude generator for emails local@domain.tld
        return /[a-zA-Z0-9._%+-]{1,32}/.test(l) && /[a-zA-Z0-9.-]{1,32}/.test(d) && /[a-zA-Z]{2,7}/.test(t);
      }),
      async ([local, domain, tld]) => {
        const raw = `  ${local}@${domain}.${tld}  `;
        const e1 = makeEmail(raw) as unknown as string;
        const e2 = makeEmail(e1) as unknown as string;
        expect(e1).toBe(e2);
        expect(e1).toBe(e1.trim().toLowerCase());
      }
    ), { numRuns: 25 });
  });
});

