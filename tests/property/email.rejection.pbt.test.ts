import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { makeEmail } from '../../src/lib/email';

describe('PBT: makeEmail rejections for invalid formats', () => {
  it('rejects strings without @ or with spaces', async () => {
    await fc.assert(fc.asyncProperty(
      fc.oneof(
        fc.string({ minLength: 1, maxLength: 16 }).filter(s => !s.includes('@')),
        fc.string({ minLength: 3, maxLength: 16 }).map(s => ` ${s} @example.com`)
      ),
      async (s) => {
        let ok = true;
        try { makeEmail(s); } catch { ok = false; }
        expect(ok).toBe(false);
      }
    ), { numRuns: 40 });
  });
});

