import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { toMessage } from '../../src/utils/error-utils';

describe('PBT: error-utils toMessage idempotency', () => {
  it('toMessage(toMessage(x)) === toMessage(x) for arbitrary strings', async () => {
    await fc.assert(
      fc.asyncProperty(fc.string(), async (s) => {
        const m1 = toMessage(s as unknown as Error);
        const m2 = toMessage(m1 as unknown as Error);
        expect(m2).toBe(m1);
      }),
      { numRuns: 50 }
    );
  });
});

