import fc from 'fast-check';

// NOTE: ドキュメント用サンプル。実行環境が整うまで skip。
describe.skip('property: web api reservation', () => {
  it('idempotent request does not double-book', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.uuid(),
        fc.integer({ min: 1, max: 3 }),
        async (requestId, qty) => {
          // arrange/act/assert: 実装後に埋める
        },
      ),
      { numRuns: 10 },
    );
  });
});
