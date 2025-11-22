import fc from 'fast-check';
import { reservationArb, defaultRuns } from './fast-check.config';

// NOTE: 足場用。実装前なので skip。
describe.skip('property: web api reservation', () => {
  it('idempotent request does not double-book', async () => {
    await fc.assert(
      fc.asyncProperty(reservationArb, async ({ requestId, sku, quantity, userId }) => {
        // arrange/act/assert: 実装後に埋める
        void requestId;
        void sku;
        void quantity;
        void userId;
      }),
      { numRuns: defaultRuns },
    );
  });
});
