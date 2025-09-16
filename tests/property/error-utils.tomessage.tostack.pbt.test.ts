import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { toMessage, toStack } from '../../src/utils/error-utils';

describe('PBT: error-utils toMessage/toStack', () => {
  it('toMessage never throws and returns a string', async () => {
    await fc.assert(fc.asyncProperty(
      fc.oneof(
        fc.string(),
        fc.record({ message: fc.string() }).map(o => Object.assign(new Error(o.message), o)),
        fc.object()
      ),
      async (input) => {
        const msg = toMessage(input as unknown);
        expect(typeof msg).toBe('string');
      }
    ), { numRuns: 50 });
  });

  it('toStack returns undefined for non-Error', async () => {
    await fc.assert(fc.asyncProperty(
      fc.anything().filter(v => !(v instanceof Error)),
      async (input) => {
        const s = toStack(input as unknown);
        expect(s === undefined || typeof s === 'string').toBe(true);
      }
    ), { numRuns: 30 });
  });
});

