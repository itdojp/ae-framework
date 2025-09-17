import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { toStack } from '../../src/utils/error-utils';

describe('PBT: error-utils toStack null-safety', () => {
  it('toStack returns undefined for non-Error values', async () => {
    await fc.assert(
      fc.asyncProperty(fc.anything(), async (v) => {
        if (v instanceof Error) return; // skip actual Error
        const st = toStack(v);
        expect(st).toBeUndefined();
      }),
      { numRuns: 50 }
    );
  });
});

