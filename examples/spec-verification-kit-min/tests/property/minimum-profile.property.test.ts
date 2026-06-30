import { describe, expect, it } from 'vitest';
import fc from 'fast-check';

// @trace:REQ-SVK-001
describe('minimum Spec & Verification Kit property example', () => {
  it('preserves positive reservation quantities', () => {
    fc.assert(
      fc.property(fc.integer({ min: 1, max: 100 }), (quantity) => {
        const result = { quantity, accepted: quantity > 0 };
        expect(result.accepted).toBe(true);
        expect(result.quantity).toBeGreaterThan(0);
      }),
      { numRuns: 16, seed: 3551 }
    );
  });
});
