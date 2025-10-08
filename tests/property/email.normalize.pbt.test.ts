import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { makeEmail } from '../../src/lib/email';

describe('PBT: makeEmail normalization', () => {
  it('trims and lowercases valid simple emails', async () => {
    const localChars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._+-';
    const arbLocal = fc
      .stringOf(fc.constantFrom(...localChars.split('')), { minLength: 1, maxLength: 10 })
      .filter((local) => /^[A-Za-z0-9](?:[A-Za-z0-9._+-]*[A-Za-z0-9])?$/.test(local));
    await fc.assert(fc.asyncProperty(
      arbLocal,
      async (local) => {
        const raw = `  ${local}@Example.COM  `;
        const res = makeEmail(raw) as unknown as string;
        expect(res).toBe(`${local.toLowerCase()}@example.com`);
      }
    ), { numRuns: 50 });
  });

  it('rejects obvious invalid emails (no @)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.string({ minLength: 1, maxLength: 12 }).filter(s => !s.includes('@')),
      async (s) => {
        let ok = true;
        try { makeEmail(s); } catch { ok = false; }
        expect(ok).toBe(false);
      }
    ), { numRuns: 30 });
  });
});
