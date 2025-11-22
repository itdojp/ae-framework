# Web API + DB フロー（人間のみで回す場合）

## 前提
- Node.js 20+, pnpm, DBコンテナ(ローカル)が使えること
- リポ構成: `spec/*`, `tests/*`, `src/web-api/*`

## 手順
1. 仕様策定
   - `spec/api/openapi.yml` を編集（エンドポイント/スキーマ）
   - `spec/bdd/web-api-sample.md` にシナリオを追加（happy/edge）
   - `spec/properties/web-api-sample.md` に不変条件を追記
2. テスト準備
   - `tests/integration/web-api/*.test.ts` にシナリオ対応のテストを追加（skip可）
   - `tests/property/web-api/README-web-api-sample.md` にプロパティ試験の方針を記述
3. 実装
   - `src/web-api/` に handler/service/repo を実装、DBマイグレーションを追加
4. 検証
   - `pnpm run lint`
   - `pnpm run test:fast`
   - `pnpm run test:integration -- --runInBand`
   - `pnpm run test:property -- --runInBand --maxWorkers=50%`
   - 任意: `STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick`
   - 任意: キャッシュ/トレンド比較
     - `node scripts/pipelines/sync-test-results.mjs --store`
     - `node scripts/pipelines/sync-test-results.mjs --snapshot`
     - `node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json`
5. PR
   - PR テンプレの Spec/Tests/Cache セクションを埋める
   - 必要なら trend JSON を添付

## 補足
- 重い検証は `--runInBand` + `--maxWorkers=50%` などでメモリを抑制。
- DB 初期化は `tests/integration` 側の fixture で可能なら in-memory を優先。
