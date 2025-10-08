# Full E2E Demo (2025-10-09)

## 概要
Verify Lite → Pact → API fuzz → Mutation quick → BDD/MBT smoke を一気通貫で走らせるための手順を整理します。`pnpm pipelines:full` をベースに、必要に応じて個別ステップへ分岐します。

## 前提
- `pnpm install`
- OpenTelemetry 環境変数は未設定でも OK（Verify Lite がスタブ化済み）
- Pact CLI / Schemathesis を利用する場合は Docker Desktop or Podman を起動

## 手順
1. **Verify Lite**
   ```bash
   pnpm verify:lite
   ```
2. **Pact Provider**
   ```bash
   pnpm pipelines:pact --contract=contracts/reservations-consumer.json
   ```
3. **API fuzz (CLI fuzz harness)**
   ```bash
   pnpm pipelines:api-fuzz --spec tests/cli/fuzz.spec.ts
   ```
4. **Mutation quick (EnhancedStateManager)**
   ```bash
   pnpm pipelines:mutation:quick -- --mutate src/utils/enhanced-state-manager.ts
   ```
5. **BDD smoke**
   ```bash
   pnpm bdd --tags "@smoke"
   ```
6. **MBT smoke**
   ```bash
   node tests/mbt/run.js --smoke
   ```

## `pipelines:full` の使いどころ
- Verify Lite 後に Pact/API fuzz/Mutation を連続実行したい場合:
  ```bash
  pnpm pipelines:full --mutation-target=src/utils/enhanced-state-manager.ts
  ```
- 重いステップを後回しにする場合:
  ```bash
  pnpm pipelines:full --skip=api-fuzz,mutation
  ```

## レポート
- Verify Lite: `reports/verify-lite/`
- Pact: `reports/contracts/`
- API fuzz: `reports/api-fuzz/`
- Mutation quick: `reports/mutation/`
- BDD/MBT: `reports/bdd/`, `reports/mbt/`

## CI 組み込みのメモ
- Verify Lite ジョブは常時実行。Pact/API fuzz/Mutation はラベル `run-full-pipeline` を付与した PR で opt-in。
- `pipelines:full --skip=api-fuzz` をベースに matrix ジョブ化し、heavy load を夜間ジョブへ移す計画。
- Mutation quick の Step Summary は `reports/mutation/mutation.json` から抽出し、Verify Lite のサマリーに統合予定。
