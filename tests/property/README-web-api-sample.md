# Web API property tests 方針（サンプル）

> ドキュメント目的。実行用テストは未実装です。

- Generators: fast-check で requestId/quantity/inventory を生成予定
- Invariants: idempotency, non-negative stock, audit on error
- Runner: `pnpm run test:property -- --runInBand --maxWorkers=50%` を想定
