# E2E Demo: Inventory Reservation (BDD / Pact / Property / MBT)

## 目的
Inventory reservation ドメインを単一シナリオとして捉え、BDD / Pact / Property / MBT を連動して実行する最小デモを提供する。

## 対象の対応表
- BDD: `specs/bdd/features/inventory_reservation.feature`
- BDD steps: `specs/bdd/steps/reservations.steps.js`
- Pact contracts: `contracts/reservations-*.json`
- Property tests: `tests/property/web-api/reservation.spec.ts`
- MBT harness: `tests/mbt/run.js`

## 実行手順（ローカル）
1. BDD
   - `pnpm run bdd`
2. Pact
   - `pnpm run pipelines:pact`
3. Property (web api)
   - `pnpm run test:property:webapi`
4. MBT
   - `pnpm run test:mbt:ci`

## 一括実行（推奨）
- `pnpm run pipelines:e2e-demo`

### オプション
- `--dry-run` : 実行せずコマンドのみ表示
- `--skip=<id>` : 特定ステップをスキップ
  - 例: `pnpm run pipelines:e2e-demo -- --skip=property,mbt`
  - step id: `bdd`, `pact`, `property`, `mbt`

## 出力
- `artifacts/e2e-demo/summary.json` に実行結果を記録

## 補足
- 上記の各検証は同一ドメイン（inventory reservation）を対象とするため、デモ時は同一PRでの変更差分を追いやすい。
- 失敗時は該当ステップの成果物（Pact report / MBT summary 等）を個別に確認する。
