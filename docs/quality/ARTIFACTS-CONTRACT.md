---
docRole: ssot
lastVerified: '2026-03-23'
owner: quality-ops
verificationCommand: pnpm -s run check:doc-consistency
---
# Artifacts/Reports 契約（Required / Optional）

> Language / 言語: English | 日本語

---

## English

Defines the minimum contract for CI-generated artifacts and reports so that missing or invalid outputs are detected early.

### 1. Purpose
- This document defines the contract and validation rules for `artifacts/` and `reports/`.
- `docs/maintenance/repo-layout-policy.md` defines placement and tracked vs non-tracked policy.
- When the two documents differ, placement and tracking rules follow the repo layout policy, while schema and consumer rules follow this document.
- `artifacts/` can contain runtime output, committed contract artifacts, reference snapshots, archives, and local debug archives at the same time.

#### 1.1 Terminology note
- The `contract` in this document means the artifacts contract for required and optional outputs.
- It is different from:
  - design-by-contract semantics such as preconditions, postconditions, or invariants
  - API or integration contracts such as Pact-based compatibility checks
- Use `docs/quality/contract-taxonomy.md` as the terminology baseline when these concepts need to be distinguished.

#### 1.2 Responsibility split with repo layout policy
- This document defines contract and validation rules for `artifacts/` and `reports/`.
- `docs/maintenance/repo-layout-policy.md` defines placement rules and tracked vs non-tracked policy.
- If they differ:
  - placement and tracked/non-tracked decisions follow the repo layout policy
  - schema and consumer expectations follow this document
- `artifacts/codex/**` is primarily an ignored-by-default local debug archive. The current repository still keeps some tracked historical entries in place, and those exceptions are inventoried in `docs/maintenance/artifact-reference-layout-plan.md`. New runtime-output archives that must be intentionally tracked should follow the repo layout policy and prefer `artifacts/archive/**`.
- For tracked reference snapshots and migration sequencing, use `docs/maintenance/artifact-reference-layout-plan.md`.

### 2. Required artifacts
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - producer: `pnpm run verify:lite`
  - validation: JSON parse + schema
  - role: summary of the verify-lite run
- `artifacts/report-envelope.json`
  - producer: `scripts/trace/create-report-envelope.mjs`
  - validation: JSON parse + schema
  - role: report envelope generated from verify-lite evidence

Schema validation is already part of `verify-lite.yml`. This document makes existence and minimum consistency explicit.

### 3. Common metadata
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/formal/formal-summary-v1.json`
- `artifacts/formal/formal-summary-v2.json`

These artifacts should carry shared `metadata`.

- common schema: `schema/artifact-metadata.schema.json`
- primary fields:
  - `generatedAtUtc`
  - `generatedAtLocal`
  - `timezoneOffset`
  - `gitCommit`
  - `branch`
  - `runner`
  - `toolVersions`

If `formal/summary.json` is kept as a legacy compatibility input, applying equivalent metadata is still recommended.

### 4. Assurance provenance minimum
- `verify:assurance` is a summary-generation command and is report-only by default.
- `verify-lite.yml` generates `artifacts/assurance/assurance-summary.{json,md}` in report-only mode.
- Strict assurance enforcement is added only when the `enforce-assurance` label is present.
- The current minimum provenance classes are:
  - `spec-derived`
  - `source-derived`
  - `model-derived`
  - `runtime-derived`
  - `manual`
- Full schema enforcement currently stops at the common artifact metadata.
- Detailed lineage such as `derived-from input`, `prompt`, `seed`, or replay command remains a docs-first rule and is separated from strict schema enforcement.

### 5. Optional artifact categories
Representative optional artifacts include the following groups.

- formal / conformance
  - `artifacts/hermetic-reports/conformance/summary.json`
  - `artifacts/hermetic-reports/formal/summary.json`
  - `artifacts/formal/formal-summary-v1.json`
  - `artifacts/formal/formal-summary-v2.json`
- assurance / scorecard / handoff
  - `artifacts/assurance/assurance-summary.{json,md}`
  - `artifacts/quality/quality-scorecard.{json,md}`
  - `artifacts/agents/hook-feedback.{json,md}`
  - `artifacts/handoff/ae-handoff.{json,md}`
- CI / automation observability
  - `artifacts/ci/policy-gate-summary.{json,md}`
  - `artifacts/ci/policy-shadow-compare-v1.json`
  - `artifacts/ci/harness-health.{json,md}`
  - `artifacts/automation/weekly-failure-summary.json`
  - `artifacts/automation/weekly-alert-summary.json`
- Context Pack / Discovery Pack
  - `artifacts/context-pack/*-report.{json,md}`
  - `artifacts/discovery-pack/discovery-pack-validate-report.{json,md}`
  - `artifacts/discovery-pack/discovery-pack-compile-report.{json,md}`
  - `artifacts/discovery-pack/plan-to-spec-normalized.md`
  - `artifacts/discovery-pack/context-pack-scaffold.yaml`
- release / trace / benchmark
  - `artifacts/release/release-plan.{json,md}`
  - `artifacts/release/post-deploy-verify.{json,md}`
  - `artifacts/hermetic-reports/trace/**`
  - `artifacts/reference/benchmarks/bench.json`
  - `artifacts/bench-compare.{json,md}`

The authoritative details remain in the Japanese section and the contract catalog. This English section mirrors the operational shape and entrypoints.

#### 5.1 Formal Summary v1/v2 dual-write migration
- Producers run `scripts/formal/generate-formal-summary-v1.mjs` with both `--out` (v1) and `--out-v2` (v2), so `artifacts/formal/formal-summary-v1.json` and `artifacts/formal/formal-summary-v2.json` are emitted in parallel.
- The main execution paths are `.github/workflows/verify-lite.yml` and `.github/workflows/formal-aggregate.yml`.
- Validators currently combine:
  - `scripts/ci/validate-formal-summary-v1.mjs`
  - `scripts/ci/validate-formal-summary-v2.mjs`
  - `scripts/ci/validate-artifacts-ajv.mjs`
- Current consumers include `scripts/ci/generate-run-manifest.mjs`, which keeps `formalSummaryV1` and `formalSummaryV2` available during the migration period.

#### 5.2 Report-only scope
- Common required fields such as `traceId`, `timestamp`, `actor`, and `event` are still treated as report-only checks in the current rollout and are not promoted to required artifacts yet.
- Equality between NDJSON and OTLP artifact sets for KvOnce trace validation remains regression-detection evidence, not a required artifact contract.
- Therefore branch protection required checks are not changed by these trace/report-only contracts.

### 6. Validation entrypoints
```bash
# Validate artifact schemas in non-strict mode
pnpm run artifacts:validate

# Strict artifact validation
pnpm run artifacts:validate -- --strict

# Check required artifacts
node scripts/ci/check-required-artifacts.mjs

# Strict required-artifact check with explicit inputs
REQUIRED_ARTIFACTS=artifacts/verify-lite/verify-lite-run-summary.json,artifacts/report-envelope.json \
REQUIRED_ARTIFACTS_STRICT=1 \
node scripts/ci/check-required-artifacts.mjs --strict
```

### 7. Related references
- `docs/maintenance/repo-layout-policy.md`
- `docs/maintenance/artifact-reference-layout-plan.md`
- `docs/quality/assurance-lanes.md`
- `docs/quality/contract-taxonomy.md`
- `docs/reference/CONTRACT-CATALOG.md`

---

## 日本語

## 1. 目的
CIが生成する成果物（artifacts/reports）について **最低限の契約（contract）** を定義し、missing/invalid を早期に検出できるようにします。

### 1.1 用語の注記
- 本ドキュメントでの contract は **Artifacts contract**（成果物の必須/任意ルール）を指します。
- DbC（Design contract: pre/post/invariant）や API/Integration contract（Pact）とは別概念です。
- 用語の基準は `docs/quality/contract-taxonomy.md` を参照してください。

### 1.2 本書と repo layout policy の責務分担
- 本書は `artifacts/` / `reports/` の **contract / validation rule** を定義します。
- `docs/maintenance/repo-layout-policy.md` は **配置・tracked/non-tracked の原則** を定義します。
- `artifacts/` には runtime output / committed contract artifact / reference snapshot / archive / local debug archive が混在します。commit 対象の可否は repo layout policy を優先し、schema/consumer 契約は本書を優先します。
- `artifacts/codex/**` は基本的には `.gitignore` で無視される local debug archive です。ただし current repository にはそのまま追跡している historical entry があり、例外一覧は `docs/maintenance/artifact-reference-layout-plan.md` で管理します。新たに runtime output を意図的に tracked archive 化する場合は、repo layout policy に従い `artifacts/archive/**` を優先します。
- tracked reference snapshot / archive の inventory と移動順序は `docs/maintenance/artifact-reference-layout-plan.md` を参照します。

## 2. Required（必須）成果物

| 成果物 | 生成元 | 検証 | 備考 |
| --- | --- | --- | --- |
| `artifacts/verify-lite/verify-lite-run-summary.json` | `pnpm run verify:lite` | JSON parse + schema | verify-lite の要約 |
| `artifacts/report-envelope.json` | `scripts/trace/create-report-envelope.mjs` | JSON parse + schema | verify-lite で生成されるレポート封筒 |

> スキーマ検証は既に `verify-lite.yml` に含まれています。  
> 本ドキュメントは「**存在と最低限の整合性**」を必須化する目的です。

### 成果物メタデータ（共通）
- `artifacts/verify-lite/verify-lite-run-summary.json` と Formal Summary v1/v2（`artifacts/formal/formal-summary-v1.json`, `artifacts/formal/formal-summary-v2.json`）には `metadata` を付与します。
- legacy compatibility input として `formal/summary.json` を扱う場合も、同等の `metadata` を付与する運用を推奨します。
- 共通スキーマ: `schema/artifact-metadata.schema.json`
- 主要フィールド: `generatedAtUtc`, `generatedAtLocal`, `timezoneOffset`, `gitCommit`, `branch`, `runner`, `toolVersions`

### assurance provenance minimum
- `verify:assurance` 自体は summary 生成コマンドであり、既定運用は report-only です。
- `verify-lite.yml` は report-only で `artifacts/assurance/assurance-summary.{json,md}` を生成します。
- `enforce-assurance` ラベル時のみ、`scripts/ci/enforce-assurance-summary.mjs` による strict assurance enforcement を追加で実行します。
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
| `artifacts/reference/benchmarks/bench.json` | `pnpm exec tsx src/cli.ts bench` を実行した場合 | TS baseline 計測成果物（schema: `schema/benchmark-report.schema.json`）。現状は legacy compatibility shim 経由 |
| `artifacts/bench-compare.json` | `scripts/quality/bench-compare.mjs` を実行した場合 | 比較判定成果物（schema: `schema/bench-compare.schema.json`） |
| `artifacts/bench-compare.md` | `scripts/quality/bench-compare.mjs` を実行した場合 | 比較判定のMarkdown要約 |
| `artifacts/assurance/assurance-summary.json` | `pnpm run verify:assurance` または `verify-lite.yml` の assurance 集約を実行した場合 | assurance lane coverage / independence warning の集約結果（schema: `schema/assurance-summary.schema.json`）。`enforce-assurance` 時の strict 判定入力にもなる |
| `artifacts/assurance/assurance-summary.md` | `pnpm run verify:assurance` または `verify-lite.yml` の assurance 集約を実行した場合 | assurance lane coverage / independence warning の Markdown 要約。PR / release / post-deploy summary の表示元 |
| `artifacts/formal/formal-summary-v1.json` | formal aggregate または verify-lite（`run-formal`）を実行した場合 | Formal Summary v1（normalized、スキーマ: `schema/formal-summary-v1.schema.json`） |
| `artifacts/formal/formal-summary-v2.json` | formal aggregate または verify-lite（`run-formal`）を実行した場合 | Formal Summary v2（`schemaVersion: formal-summary/v2`, `contractId: formal-summary.v2`、スキーマ: `schema/formal-summary-v2.schema.json`） |
| `artifacts/release/release-plan.json` | `ae release plan` または `post-deploy-verify.yml` を実行した場合 | release plan の機械可読成果物（schemaVersion: `ae-release-plan/v1`） |
| `artifacts/release/release-plan.md` | `ae release plan` または `post-deploy-verify.yml` を実行した場合 | release plan の運用向け要約 |
| `artifacts/release/post-deploy-verify.json` | `ae release verify` または `post-deploy-verify.yml` を実行した場合 | post-deploy 判定成果物（schemaVersion: `ae-post-deploy-verify/v1`） |
| `artifacts/release/post-deploy-verify.md` | `ae release verify` または `post-deploy-verify.yml` を実行した場合 | post-deploy 判定の運用向け要約 |
| `artifacts/ci/policy-gate-summary.json` | `policy-gate.yml` を実行した場合 | policy gate 判定の機械可読成果物（schemaVersion: `policy-gate-summary/v1`, contractId: `policy-gate-summary.v1`） |
| `artifacts/ci/policy-gate-summary.md` | `policy-gate.yml` を実行した場合 | policy gate 判定の Markdown 要約 |
| `artifacts/ci/policy-shadow-compare-v1.json` | `policy-gate.yml` を `AE_POLICY_ENGINE_MODE=shadow` または compare 有効で実行した場合 | JS decision と OPA shadow compare の diff 成果物。shadow mismatch 傾向の観測入力 |
| `artifacts/ci/harness-health.json` | `pr-ci-status-comment.yml` の `summarize` job、または `ci-extended.yml` の schedule 実行で harness health を生成した場合 | harness gate の機械可読成果物（schemaVersion: `harness-health/v1`, contractId: `harness-health.v1`）。`hook-feedback`、`change-package`、PR summary が参照する |
| `artifacts/ci/harness-health.md` | `pr-ci-status-comment.yml` の `summarize` job、または `ci-extended.yml` の schedule 実行で harness health を生成した場合 | harness gate の Markdown 要約。PR summary と週次 CI stability review の表示元 |
| `artifacts/quality/quality-scorecard.json` | `scripts/quality/build-quality-scorecard.mjs`、または `verify-lite.yml` の scorecard 集約を実行した場合 | verify-lite / report-envelope / optional assurance・formal・policy・harness・bench を横断集約する report-only scorecard（schema: `schema/quality-scorecard.schema.json`） |
| `artifacts/quality/quality-scorecard.md` | `scripts/quality/build-quality-scorecard.mjs`、または `verify-lite.yml` の scorecard 集約を実行した場合 | scorecard の Markdown 要約。verify-lite Step Summary と PR summary append の表示元 |
| `artifacts/agents/hook-feedback.json` | `pr-ci-status-comment.yml` の `summarize` job が同一 head SHA の `verify-lite-report` を取得できた場合、または `pnpm run hook-feedback:build` を実行した場合 | continuation 用の正規化 JSON（schema: `schema/hook-feedback.schema.json`）。verify-lite / harness-health / change-package / optional assurance を要約する |
| `artifacts/agents/hook-feedback.md` | `pr-ci-status-comment.yml` の `summarize` job が同一 head SHA の `verify-lite-report` を取得できた場合、または `pnpm run hook-feedback:build` を実行した場合 | continuation 用の Markdown 要約。PR summary へ追記される |
| `artifacts/handoff/ae-handoff.json` | `pnpm run handoff:create` を実行した場合 | AE-HANDOFF の機械可読 sidecar（schema: `schema/ae-handoff.schema.json`）。既存 `hook-feedback` / verify-lite evidence を deterministic に handoff package 化する |
| `artifacts/handoff/ae-handoff.md` | `pnpm run handoff:create` を実行した場合 | AE-HANDOFF の Markdown sidecar。PR / Issue handoff コメントへ転記する基礎フォーマット |
| `artifacts/ci/automation-report.json` | codex/autopilot 系 workflow で `AE_AUTOMATION_REPORT_FILE` を設定した場合 | 自動化実行サマリ（schemaVersion: `ae-automation-report/v1`） |
| `artifacts/automation/weekly-failure-summary.json` | `automation-observability-weekly.yml` を実行した場合 | 週次 automation observability 集計。SLO / MTTR / top failure reason codes を保持する report-only 成果物 |
| `artifacts/automation/weekly-alert-summary.json` | `automation-observability-weekly.yml` を実行した場合 | 通知判定結果。suppression / cooldown / alert decision の確認入力 |
| `artifacts/context-pack/context-pack-boundary-map-report.json` | `pnpm run context-pack:verify-boundary-map` を実行した場合 | boundary-map sidecar と Context Pack の参照整合、missing slice / duplicate producer / cycle / skipped auxiliary file を検証する report-only JSON |
| `artifacts/context-pack/context-pack-boundary-map-report.md` | `pnpm run context-pack:verify-boundary-map` を実行した場合 | boundary-map 検証の Markdown 要約。missing slice / duplicate producer / cycle / skipped auxiliary file の operator review 用 |
| `artifacts/context-pack/context-pack-functor-report.json` | context-pack functor 検証を実行した場合 | `scripts/context-pack/verify-functor.mjs` の JSON レポート（違反種別・対象 object/morphism を含む） |
| `artifacts/context-pack/context-pack-functor-report.md` | context-pack functor 検証を実行した場合 | `scripts/context-pack/verify-functor.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-natural-transformation-report.json` | context-pack natural transformation 検証を実行した場合 | `scripts/context-pack/verify-natural-transformation.mjs` の JSON レポート（可換チェック/禁止変更連携の違反種別を含む） |
| `artifacts/context-pack/context-pack-natural-transformation-report.md` | context-pack natural transformation 検証を実行した場合 | `scripts/context-pack/verify-natural-transformation.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-product-coproduct-report.json` | context-pack product/coproduct 検証を実行した場合 | `scripts/context-pack/verify-product-coproduct.mjs` の JSON レポート（入力必須項目/失敗variant網羅/証跡不足を含む） |
| `artifacts/context-pack/context-pack-product-coproduct-report.md` | context-pack product/coproduct 検証を実行した場合 | `scripts/context-pack/verify-product-coproduct.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-phase5-report.json` | context-pack Phase5+ テンプレ検証を実行した場合 | `scripts/context-pack/verify-phase5-templates.mjs` の JSON レポート（pullback/pushout/monoidal/kleisli の参照・証跡・境界違反を含む） |
| `artifacts/context-pack/context-pack-phase5-report.md` | context-pack Phase5+ テンプレ検証を実行した場合 | `scripts/context-pack/verify-phase5-templates.mjs` の Markdown 要約 |
| `artifacts/discovery-pack/discovery-pack-validate-report.json` | `pnpm run discovery-pack:validate` または `verify-lite.yml` の Discovery validate 観測を実行した場合 | Discovery Pack validate の report-only JSON。`blocking-open-questions` / orphan approved requirement/business use case / strict-approved の集計を保持する |
| `artifacts/discovery-pack/discovery-pack-validate-report.md` | `pnpm run discovery-pack:validate` または `verify-lite.yml` の Discovery validate 観測を実行した場合 | Discovery Pack validate の Markdown 要約。report-only / strict rollout の operator review 用 |
| `artifacts/discovery-pack/discovery-pack-compile-report.json` | `pnpm run discovery-pack:compile -- --target <plan-spec|context-pack-scaffold>` または `verify-lite.yml` の strict Discovery compile dry-run を実行した場合 | compile 対象件数、status 除外件数、target 別 skip 件数を含む JSON 要約 |
| `artifacts/discovery-pack/discovery-pack-compile-report.md` | `pnpm run discovery-pack:compile -- --target <plan-spec|context-pack-scaffold>` または `verify-lite.yml` の strict Discovery compile dry-run を実行した場合 | compile 対象件数と除外理由の Markdown 要約 |
| `artifacts/discovery-pack/plan-to-spec-normalized.md` | `pnpm run discovery-pack:compile -- --target plan-spec` または strict compile dry-run を実行した場合 | plan-to-spec 正規化 Markdown。non-authoritative な生成物であり、repo SSOT へは手動昇格する |
| `artifacts/discovery-pack/context-pack-scaffold.yaml` | `pnpm run discovery-pack:compile -- --target context-pack-scaffold` を実行した場合 | Context Pack SSOT の下書き scaffold。`schema/context-pack-v1.schema.json` 互換だが authoritative ではない |
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

# Quality Scorecard の validate（ローカル）
node scripts/ci/validate-quality-scorecard.mjs \
  artifacts/quality/quality-scorecard.json \
  schema/quality-scorecard.schema.json

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
- `verify-lite.yml` 自体は従来どおり **必須ステータスチェック（merge-blocking）** のまま維持しつつ、その内部に assurance summary の生成/検証ステップを **non-blocking（continue-on-error; 観測フェーズ）** として追加
- `verify-lite.yml` は `artifacts/verify-lite/verify-lite-run-summary.json` を入力に `artifacts/assurance/assurance-summary.{json,md}` を **report-only / non-blocking** で生成し、artifact upload と Step Summary に含める
- `verify-lite.yml` は同じ required input を使って `artifacts/quality/quality-scorecard.{json,md}` を **report-only / non-blocking** で生成し、artifact upload と Step Summary に含める
- `enforce-assurance` ラベル時は `verify-lite.yml` の `Enforce assurance summary (strict; label-gated)` ステップが `scripts/ci/enforce-assurance-summary.mjs` を呼び出し、`artifacts/assurance/assurance-summary.json` に対して strict assurance enforcement を実行する
- `pr-ci-status-comment.yml` / `scripts/summary/render-pr-summary.mjs` は `artifacts/assurance/assurance-summary.json` が存在する場合、PR summary comment に assurance の要約（satisfied claims / warning claims / warning codes）を追記する
- `pr-ci-status-comment.yml` / `scripts/summary/render-pr-summary.mjs` は `artifacts/quality/quality-scorecard.{json,md}` が存在する場合、PR summary comment に overall status / score / blockers を追記する
- `post-deploy-verify.yml` は release artifact bundle 内に `artifacts/assurance/assurance-summary.md` が存在する場合、Step Summary に assurance 要約を追記する。これは optional / report-only であり、release verify の gate 判定は変えない
- manual `post-deploy-verify.yml` で release 側の assurance summary を使う場合は、公開済み release asset `quality-artifacts.tgz` を取得するため `release_tag` が必要
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
- `scripts/ci/validate-quality-scorecard.mjs`
- `schema/artifact-metadata.schema.json`
- `schema/assurance-summary.schema.json`
- `schema/quality-scorecard.schema.json`
- `schema/formal-summary-v1.schema.json`
- `schema/formal-summary-v2.schema.json`
- `docs/quality/assurance-operations-runbook.md`
- `docs/reference/CONTRACT-CATALOG.md`
- `docs/quality/path-normalization-contract.md`
- `docs/quality/run-manifest-freshness-contract.md`
