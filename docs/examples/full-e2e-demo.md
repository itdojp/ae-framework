# Full E2E Demo: Spec → Tests → Runtime

このドキュメントは、`ae-framework` のサンプル資産を組み合わせて「仕様→テスト→コード→検証」までを一貫して再現する手順をまとめたものです。Verify Lite / Mutation Quick / Pact / MBT / BDD を連携させたいときの素振り用チェックリストとして利用できます。

> **前提**
> - Node.js 20 / pnpm 8 系が利用可能であること
> - `pnpm install` 済み
> - Podman (rootless) が利用可能であること（Pact / API fuzz などコンテナ系タスクで使用）
>   - Docker Desktop を利用する場合は `podman/compose.*` の定義を `docker compose` で実行しても同等に動作

## 1. 仕様と生成物の確認

1. KvOnce 仕様 (TLA+) を TLC/Apalache で実行:
   ```bash
   pnpm run spec:kv-once:tlc
   pnpm run spec:kv-once:apalache # ツール導入済みの場合
   ```
2. 生成物 (BDD/OpenAPI/モニタ) を差分チェック:
   ```bash
   pnpm run generate:artifacts -- --dry-run
   ```
3. 生成物の検証結果は `artifacts/` 配下と `reports/formal/` に保存される。CI では `spec-generate-model.yml` が同じ流れを実行する。

## 2. Verify Lite (ユニット/Property/Mutation)

1. Verify Lite を実行し、ユニット・Property・Mutation quick (差分) をまとめて検証:
   ```bash
   pnpm run verify:lite
   ```
2. 実行結果:
   - `verify-lite-run-summary.json` / `verify-lite-lint-summary.json`
   - Property harness サマリ `artifacts/properties/summary.json`
   - MBT サマリ `artifacts/mbt/summary.json`
   - Mutation quick レポート `reports/mutation/mutation.json`
   - サマリ JSON `reports/mutation/summary.json`（Step Summary にも同様の概要を出力）
3. CI (`verify-lite.yml`) では上記成果物をレポート Envelope 化し、`verify-lite-report` / `mutation-quick-report` / `mutation-survivors-json` などをアーティファクトとして添付する。

## 3. Mutation Quick の個別実行

Verify Lite から切り離して Mutation Quick のみを検証したい場合は、以下を利用する。

```bash
./scripts/mutation/run-scoped.sh --quick --mutate src/utils/enhanced-state-manager.ts
# 差分パターンを自動抽出
./scripts/mutation/run-scoped.sh --quick --auto-diff
```

生成物:
- `reports/mutation/mutation.json`
- `reports/mutation/index.html`
- `reports/mutation/survivors.json`

GitHub Actions (`mutation-quick.yml`) では手動トリガーで同じコマンドを実行し、アーティファクトとしてアップロードする。

## 4. BDD / Pact / API Fuzz

### 4.1 BDD テスト
```bash
pnpm run bdd:test
```
- `tests/bdd/` 配下のシナリオを Vitest 経由で実行。
- Lint/Step lint は `pnpm run bdd:lint` / `pnpm run bdd:step-lint` で個別実行可能。

### 4.2 Pact Provider 検証
```bash
pnpm run contracts:verify # scripts/contracts/verify-reservation-contract.ts
```
- Pact ファイルは `artifacts/pacts/` に配置。
- 追加契約を検証したい場合は `contracts/` 配下に JSON を追加し、同スクリプトに渡す。

### 4.3 API Fuzz / Schemathesis
```bash
make test-api-fuzz
```
- Fastify スタブを起動し、Schemathesis コンテナで OpenAPI 仕様に対する fuzz を実行。
- ログとレポートは `reports/api-fuzz/` に保存。

## 5. MBT (Model-Based Testing)

1. モデルベーステスト（在庫シミュレーション）:
   ```bash
   pnpm test:mbt
   ```
2. 生成されたケースは `artifacts/mbt/summary.json` に保存され、Verify Lite からも再利用可能。

## 6. End-to-End チェックリスト

1. `pnpm run spec:kv-once:tlc` / `pnpm run spec:kv-once:apalache`
2. `pnpm run generate:artifacts -- --dry-run`
3. `pnpm run verify:lite`
4. (任意) `./scripts/mutation/run-scoped.sh --quick --auto-diff`
5. `pnpm run bdd:test`
6. `pnpm run contracts:verify`
7. `make test-api-fuzz`
8. (任意) `pnpm test:mbt -- --runs=8 --depth=6` でシードを変えたモデル検証を追加確認
9. `pnpm pipelines:trace --input samples/trace/kvonce-sample.ndjson --skip-replay`

全て完了したら、`reports/` / `artifacts/` の差分を確認し、必要に応じて Issue / PR に最新状況をコメントしてください。

---

この手順に沿って実施し、成果物をリンク付きで Issue #999 / #1001 / #1002 / #1003 へコメントすれば、Week2〜Week4 トラッカーの「エンドツーエンドデモ」要件を満たせます。

## 7. pnpm pipelines コマンドの活用 (2025-10-09)

Verify Lite を起点に Pact / API fuzz / Mutation quick を順番に実行したい場合は、ラッパーを利用すると便利です。

- **Verify Lite → Pact → API fuzz → Mutation quick**
  ```bash
  pnpm pipelines:full --mutation-target=src/utils/enhanced-state-manager.ts
  ```
- 重いステップをスキップしたい場合:
  ```bash
  pnpm pipelines:full --skip=api-fuzz,mutation
  ```
- 個別ステップを直接呼び出す場合:
  ```bash
  pnpm pipelines:pact --contract=contracts/reservations-consumer.json
  pnpm pipelines:api-fuzz --spec tests/cli/fuzz.spec.ts
  pnpm pipelines:mutation:quick -- --mutate src/utils/enhanced-state-manager.ts
  pnpm pipelines:trace --input samples/trace/kvonce-sample.ndjson
  ```
  - 実行後は `artifacts/trace/report-envelope.json` にトレース用 Envelope が生成され、`pnpm verify:conformance --from-envelope artifacts/trace/report-envelope.json` で結果を再利用できる。

各ステップのレポート:
- Verify Lite: `reports/verify-lite/`
- Pact: `reports/contracts/`
- API fuzz: `reports/api-fuzz/`
- Mutation quick: `reports/mutation/`
- BDD/MBT: `reports/bdd/`, `reports/mbt/`

CI では Verify Lite を常設ジョブとし、Pact/API fuzz/Mutation quick はラベル `run-full-pipeline` で opt-in させる運用を想定しています。
