# Artifacts/Reports 契約（Required / Optional）

> Language / 言語: English | 日本語

---

## English (Summary)

Defines required vs optional artifacts and how to validate them in CI.

---

## 日本語

## 1. 目的
CIが生成する成果物（artifacts/reports）について **最低限の契約（contract）** を定義し、missing/invalid を早期に検出できるようにします。

### 1.1 用語の注記
- 本ドキュメントでの contract は **Artifacts contract**（成果物の必須/任意ルール）を指します。
- DbC（Design contract: pre/post/invariant）や API/Integration contract（Pact）とは別概念です。
- 用語の基準は `docs/quality/contract-taxonomy.md` を参照してください。

## 2. Required（必須）成果物

| 成果物 | 生成元 | 検証 | 備考 |
| --- | --- | --- | --- |
| `artifacts/verify-lite/verify-lite-run-summary.json` | `pnpm run verify:lite` | JSON parse + schema | verify-lite の要約 |
| `artifacts/report-envelope.json` | `scripts/trace/create-report-envelope.mjs` | JSON parse + schema | verify-lite で生成されるレポート封筒 |

> スキーマ検証は既に `verify-lite.yml` に含まれています。  
> 本ドキュメントは「**存在と最低限の整合性**」を必須化する目的です。

### 成果物メタデータ（共通）
- `artifacts/verify-lite/verify-lite-run-summary.json` と `formal/summary.json` には `metadata` を付与します。
- 共通スキーマ: `schema/artifact-metadata.schema.json`
- 主要フィールド: `generatedAtUtc`, `generatedAtLocal`, `timezoneOffset`, `gitCommit`, `branch`, `runner`, `toolVersions`

### assurance provenance minimum
- `verify:assurance` は現時点で report-only です。
- independence 判定で最低限使う provenance は次の粗い分類です。
  - `spec-derived`
  - `source-derived`
  - `model-derived`
  - `runtime-derived`
  - `manual`
- 現行 schema で全面 enforce しているのは `artifact-metadata` の共通項目までです。
- `derived-from input`, `prompt`, `seed`, `replay command` などの詳細 lineage は docs rule として先行し、schema enforcement は後続に分離します。
- 詳細は `docs/quality/assurance-lanes.md` を参照してください。

## 3. Optional（条件付き）成果物

| 成果物 | 条件 | 備考 |
| --- | --- | --- |
| `artifacts/hermetic-reports/conformance/summary.json` | conformance 検証を実行した場合 | `verify-conformance.mjs` の出力 |
| `artifacts/hermetic-reports/formal/summary.json` | formal aggregate を実行した場合 | `aggregate-formal.mjs` の出力 |
| `artifacts/hermetic-reports/formal/*-output.txt` | formal verifier を実行した場合 | 各ツールの実行ログ（全文）。Formal Summary v1/v2 の `results[].logPath` から参照される場合があります |
| `artifacts/bench.json` | `ae bench` を実行した場合 | TS baseline 計測成果物（schema: `schema/benchmark-report.schema.json`） |
| `artifacts/bench-compare.json` | `scripts/quality/bench-compare.mjs` を実行した場合 | 比較判定成果物（schema: `schema/bench-compare.schema.json`） |
| `artifacts/bench-compare.md` | `scripts/quality/bench-compare.mjs` を実行した場合 | 比較判定のMarkdown要約 |
| `artifacts/assurance/assurance-summary.json` | `pnpm run verify:assurance` または `verify-lite.yml` の report-only assurance 集約を実行した場合 | assurance lane coverage / independence warning の集約結果（schema: `schema/assurance-summary.schema.json`） |
| `artifacts/assurance/assurance-summary.md` | `pnpm run verify:assurance` または `verify-lite.yml` の report-only assurance 集約を実行した場合 | assurance lane coverage / independence warning の Markdown 要約 |
| `artifacts/formal/formal-summary-v1.json` | formal aggregate または verify-lite（`run-formal`）を実行した場合 | Formal Summary v1（normalized、スキーマ: `schema/formal-summary-v1.schema.json`） |
| `artifacts/formal/formal-summary-v2.json` | formal aggregate または verify-lite（`run-formal`）を実行した場合 | Formal Summary v2（`schemaVersion: formal-summary/v2`, `contractId: formal-summary.v2`、スキーマ: `schema/formal-summary-v2.schema.json`） |
| `artifacts/release/release-plan.json` | `ae release plan` または `post-deploy-verify.yml` を実行した場合 | release plan の機械可読成果物（schemaVersion: `ae-release-plan/v1`） |
| `artifacts/release/release-plan.md` | `ae release plan` または `post-deploy-verify.yml` を実行した場合 | release plan の運用向け要約 |
| `artifacts/release/post-deploy-verify.json` | `ae release verify` または `post-deploy-verify.yml` を実行した場合 | post-deploy 判定成果物（schemaVersion: `ae-post-deploy-verify/v1`） |
| `artifacts/release/post-deploy-verify.md` | `ae release verify` または `post-deploy-verify.yml` を実行した場合 | post-deploy 判定の運用向け要約 |
| `artifacts/ci/policy-gate-summary.json` | `policy-gate.yml` を実行した場合 | policy gate 判定の機械可読成果物（schemaVersion: `policy-gate-summary/v1`, contractId: `policy-gate-summary.v1`） |
| `artifacts/ci/policy-gate-summary.md` | `policy-gate.yml` を実行した場合 | policy gate 判定の Markdown 要約 |
| `artifacts/ci/automation-report.json` | codex/autopilot 系 workflow で `AE_AUTOMATION_REPORT_FILE` を設定した場合 | 自動化実行サマリ（schemaVersion: `ae-automation-report/v1`） |
| `artifacts/context-pack/context-pack-functor-report.json` | context-pack functor 検証を実行した場合 | `scripts/context-pack/verify-functor.mjs` の JSON レポート（違反種別・対象 object/morphism を含む） |
| `artifacts/context-pack/context-pack-functor-report.md` | context-pack functor 検証を実行した場合 | `scripts/context-pack/verify-functor.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-natural-transformation-report.json` | context-pack natural transformation 検証を実行した場合 | `scripts/context-pack/verify-natural-transformation.mjs` の JSON レポート（可換チェック/禁止変更連携の違反種別を含む） |
| `artifacts/context-pack/context-pack-natural-transformation-report.md` | context-pack natural transformation 検証を実行した場合 | `scripts/context-pack/verify-natural-transformation.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-product-coproduct-report.json` | context-pack product/coproduct 検証を実行した場合 | `scripts/context-pack/verify-product-coproduct.mjs` の JSON レポート（入力必須項目/失敗variant網羅/証跡不足を含む） |
| `artifacts/context-pack/context-pack-product-coproduct-report.md` | context-pack product/coproduct 検証を実行した場合 | `scripts/context-pack/verify-product-coproduct.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-phase5-report.json` | context-pack Phase5+ テンプレ検証を実行した場合 | `scripts/context-pack/verify-phase5-templates.mjs` の JSON レポート（pullback/pushout/monoidal/kleisli の参照・証跡・境界違反を含む） |
| `artifacts/context-pack/context-pack-phase5-report.md` | context-pack Phase5+ テンプレ検証を実行した場合 | `scripts/context-pack/verify-phase5-templates.mjs` の Markdown 要約 |
| `artifacts/hermetic-reports/trace/kvonce-events.ndjson` | `run-kvonce-conformance.sh` を実行した場合（`--format ndjson|otlp`） | KvOnce 正規化イベント。NDJSON経路/OTLP経路で同一ファイルセットを出力する契約を持つ |
| `artifacts/hermetic-reports/trace/kvonce-projection.json` | `run-kvonce-conformance.sh` を実行した場合（`--format ndjson|otlp`） | Projector 集計結果 |
| `artifacts/hermetic-reports/trace/kvonce-validation.json` | `run-kvonce-conformance.sh` を実行した場合（`--format ndjson|otlp`） | Validator 結果 |
| `artifacts/hermetic-reports/trace/projected/kvonce-state-sequence.json` | `run-kvonce-conformance.sh` を実行した場合（`--format ndjson|otlp`） | イベントごとの射影状態 |

### 3.1 Formal Summary v1/v2 の段階移行（dual-write + dual-validate）
- producer は `scripts/formal/generate-formal-summary-v1.mjs` を `--out`（v1）と `--out-v2`（v2）で同時実行し、`artifacts/formal/formal-summary-v1.json` / `artifacts/formal/formal-summary-v2.json` を並行出力します。
- 主要な実行経路は `.github/workflows/verify-lite.yml` と `.github/workflows/formal-aggregate.yml` です。
- validator は `scripts/ci/validate-formal-summary-v1.mjs` と `scripts/ci/validate-formal-summary-v2.mjs` を併用し、加えて `scripts/ci/validate-artifacts-ajv.mjs` でも両ファイルを検証します。
- consumer は `scripts/ci/generate-run-manifest.mjs`（`formalSummaryV1` / `formalSummaryV2`）です。移行期間中は v1/v2 の双方を参照可能な状態を維持します。

### 3.2 report-only 運用範囲（Issue #2391）
- 共通必須項目 `traceId` / `timestamp` / `actor` / `event` の契約確認は report-only とし、現時点では Required 成果物に昇格しません。
- NDJSON経路とOTLP経路の成果物セット一致性（`tests/unit/trace/kvonce-conformance.integration.test.ts`）は回帰検知目的で運用し、`REQUIRED_ARTIFACTS` には追加しません。
- したがって branch protection の Required checks は変更しません（既存の required 定義を維持）。

## 4. 検証スクリプト

```bash
# JSON Schema 契約を検証（既定: non-blocking）
pnpm run artifacts:validate

# JSON Schema 契約を strict モードで検証（違反で exit 1）
pnpm run artifacts:validate -- --strict

# enforce-artifacts 相当（strict）をローカル再現:
# trace/verify-lite artifacts を先に生成してから検証する
bash scripts/trace/run-kvonce-conformance.sh \
  --input samples/trace/kvonce-sample.ndjson \
  --format ndjson \
  --output-dir artifacts/hermetic-reports/trace
node scripts/ci/write-verify-lite-summary.mjs
node scripts/trace/create-report-envelope.mjs \
  artifacts/verify-lite/verify-lite-run-summary.json \
  artifacts/report-envelope.json
mkdir -p artifacts/trace
cp artifacts/report-envelope.json artifacts/trace/report-envelope.json
pnpm run artifacts:validate -- --strict

# 既定の必須成果物を確認（非厳格）
node scripts/ci/check-required-artifacts.mjs

# Formal Summary v1/v2 の dual-validate（ローカル）
node scripts/ci/validate-formal-summary-v1.mjs \
  artifacts/formal/formal-summary-v1.json \
  schema/formal-summary-v1.schema.json
node scripts/ci/validate-formal-summary-v2.mjs \
  artifacts/formal/formal-summary-v2.json \
  schema/formal-summary-v2.schema.json

# Assurance Summary の validate（ローカル）
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json

# 必須成果物を明示して厳格チェック
REQUIRED_ARTIFACTS=artifacts/verify-lite/verify-lite-run-summary.json,artifacts/report-envelope.json \
REQUIRED_ARTIFACTS_STRICT=1 \
node scripts/ci/check-required-artifacts.mjs --strict
```

`pnpm run artifacts:validate` は以下を常に出力します。
- `artifacts/schema-validation/summary.json`
- `artifacts/schema-validation/summary.md`
- `artifacts/schema-validation/errors.json`

## 5. CI統合（段階導入）
- `verify-lite.yml` に **non-blocking** で組み込み（観測フェーズ）
- `verify-lite.yml` は `artifacts/verify-lite/verify-lite-run-summary.json` を入力に `artifacts/assurance/assurance-summary.{json,md}` を report-only で生成し、artifact upload と Step Summary に含める
- 厳格化する場合は `REQUIRED_ARTIFACTS_STRICT=1` を有効化  
  - 例: PRラベル `enforce-artifacts` を条件に strict モードを有効化
- `validate-artifacts-ajv.yml` では strict（`enforce-artifacts`）時に `run-kvonce-conformance.sh`（trace artifacts）と `artifacts/verify-lite/verify-lite-run-summary.json` / `artifacts/report-envelope.json` / `artifacts/trace/report-envelope.json` を生成してから `artifacts:validate` を実行
- non-strict 時は従来どおり `artifacts:validate` のみを実行（軽量動作を維持）
- `.github/workflows/verify-lite.yml` と `.github/workflows/formal-aggregate.yml` は Formal Summary を v1/v2 の dual-write で出力し、`validate-formal-summary-v1.mjs` + `validate-formal-summary-v2.mjs` を実行（dual-validate）
- `verify-lite.yml` の必須ステップで `tests/contracts/cli-artifacts-contracts.test.ts` を実行し、主要CLIの JSON schema / exit code 契約を継続検証

## 6. 参照
- `.github/workflows/verify-lite.yml`
- `.github/workflows/formal-aggregate.yml`
- `.github/workflows/formal-verify.yml`
- `scripts/ci/check-required-artifacts.mjs`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `scripts/ci/validate-formal-summary-v1.mjs`
- `scripts/ci/validate-formal-summary-v2.mjs`
- `scripts/ci/validate-assurance-summary.mjs`
- `schema/artifact-metadata.schema.json`
- `schema/assurance-summary.schema.json`
- `schema/formal-summary-v1.schema.json`
- `schema/formal-summary-v2.schema.json`
- `docs/reference/CONTRACT-CATALOG.md`
- `docs/quality/path-normalization-contract.md`
- `docs/quality/run-manifest-freshness-contract.md`
