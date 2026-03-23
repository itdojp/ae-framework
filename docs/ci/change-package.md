---
docRole: ssot
lastVerified: '2026-03-22'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Change Package (証跡パッケージ)

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
Change Package is the standard artifact set that shifts PR safety judgment from diff-only review to evidence-oriented review.

It consumes policy and changed-file information and produces machine-readable outputs for:
- risk selection
- required labels
- reproducibility commands
- rollout and monitoring plans

Responsibility split:
- `plan-artifact/v1`: before-change review contract
- `change-package/v1`: after-change evidence contract

### 2. Outputs
- `artifacts/change-package/change-package.json`
  - schema: `change-package/v1`
  - major sections:
    - `intent`
    - `scope`
    - `risk`
    - `evidence`
    - `reproducibility`
    - `rolloutPlan`
    - `monitoringPlan`
    - `exceptions`
- `artifacts/change-package/change-package.md`
  - human-readable summary for PR discussion
- `artifacts/change-package/change-package-validation.json|md`
  - schema validation and required-evidence evaluation results

#### `change-package/v2` preview contract
- schema: `schema/change-package-v2.schema.json`
- sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- added sections:
  - `assurance`
  - `claims`
  - `assumptions`
  - `proofObligations`
  - `counterexamples`
  - `trustBoundary`
  - `runtimeControls`
  - `waivers`

At the moment, v2 is introduced as schema/docs preview only. Default generator, validator, and PR summary integration still use v1.

### 3. Generation and validation commands
```bash
# Generate
node scripts/change-package/generate.mjs \
  --policy policy/risk-policy.yml \
  --output-json artifacts/change-package/change-package.json \
  --output-md artifacts/change-package/change-package.md

# Validate (non-strict: missing evidence becomes warning)
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package.json \
  --schema schema/change-package.schema.json

# Validate (strict: missing evidence fails)
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package.json \
  --schema schema/change-package.schema.json \
  --required-evidence verifyLiteSummary,policyGateSummary \
  --strict

# Validate the v2 preview contract
node scripts/change-package/validate.mjs \
  --file fixtures/change-package/sample.change-package-v2.json \
  --schema schema/change-package-v2.schema.json
```

### 4. Main options
#### `generate.mjs`
- `--changed-files-file <path>`: explicit changed file list input
- `--event-path <path>`: GitHub event payload input
- `--artifact-root <path>`: artifact lookup root for evidence existence checks
- `--mode digest|detailed`: markdown output detail level

#### `validate.mjs`
- `--required-evidence <csv>`: explicit required evidence IDs
- `--strict`: treat required-evidence gaps as errors

### 5. CI integration
`pr-ci-status-comment.yml` performs the following:
1. generate Change Package
2. validate Change Package
3. schema-validate committed `artifacts/plan/plan-artifact.json` when present
4. append Change Package / Plan Artifact sections to the PR summary comment
5. upload the artifacts

This means:
- `pr-summary:detailed` shows richer evidence and reproducibility commands
- digest mode shows a shorter summary

When tied to auto-merge:
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` includes Change Package Validation in auto-merge eligibility
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=0` requires `PASS` and rejects `WARN`

### 6. Operational guidance
- For `risk:high` PRs, review `missingRequiredLabels` and `exceptions` first
- For `risk:high` PRs, commit `artifacts/plan/plan-artifact.json|md` before implementation so `policy-gate` sees the pre-review contract
- When `policy/risk-policy.yml` changes, verify Change Package outcomes with fixtures and tests
- When the schema changes, update `fixtures/change-package/sample.change-package.json` and `scripts/ci/validate-json.mjs` together
- Treat `change-package/v2` as a preview contract and do not break the default v1 flow

---

## 日本語

## 1. 目的

PR の安全性判断を diff 中心ではなく、証跡（evidence）中心で扱うための標準成果物です。  
`policy/risk-policy.yml` と変更差分を入力に、リスク判定・必要ラベル・再現コマンド・監視計画を機械可読で出力します。

責務分離:
- `plan-artifact/v1`: before-change review（何を変える予定か）
- `change-package/v1`: after-change evidence（何が変わり、どの証跡が揃ったか）

## 2. 出力物

- `artifacts/change-package/change-package.json`
  - スキーマ: `change-package/v1`
  - 主要項目:
    - `intent`: 変更意図
    - `scope`: 変更ファイル数・対象領域
    - `risk`: selected / inferred / required labels / 根拠
    - `evidence`: verify-lite / policy-gate / harness-health などの存在確認
    - `reproducibility`: 再現コマンド
    - `rolloutPlan`, `monitoringPlan`, `exceptions`
- `artifacts/change-package/change-package.md`
  - PR サマリに貼り込む人間向け要約
- `artifacts/change-package/change-package-validation.json|md`
  - schema 検証と required evidence 判定の結果

### `change-package/v2`（Phase 1 preview contract）

- スキーマ: `schema/change-package-v2.schema.json`
- sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- 追加セクション:
  - `assurance`
  - `claims`
  - `assumptions`
  - `proofObligations`
  - `counterexamples`
  - `trustBoundary`
  - `runtimeControls`
  - `waivers`

現時点では、v2 は schema/docs の先行導入です。既定の generator / validator / PR summary 連携は引き続き v1 を使用します。

## 3. 生成・検証コマンド

```bash
# 生成
node scripts/change-package/generate.mjs \
  --policy policy/risk-policy.yml \
  --output-json artifacts/change-package/change-package.json \
  --output-md artifacts/change-package/change-package.md

# 検証（非strict: missing evidence は warning）
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package.json \
  --schema schema/change-package.schema.json

# 検証（strict: missing evidence で fail）
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package.json \
  --schema schema/change-package.schema.json \
  --required-evidence verifyLiteSummary,policyGateSummary \
  --strict

# v2 preview contract の schema validate
node scripts/change-package/validate.mjs \
  --file fixtures/change-package/sample.change-package-v2.json \
  --schema schema/change-package-v2.schema.json
```

## 4. オプション（主なもの）

### `generate.mjs`
- `--changed-files-file <path>`: 変更ファイル一覧（改行区切り）を明示入力
- `--event-path <path>`: GitHub event payload の入力
- `--artifact-root <path>`: evidence 存在確認のルート
- `--mode digest|detailed`: Markdown 出力粒度

### `validate.mjs`
- `--required-evidence <csv>`: required evidence ID を明示
- `--strict`: required evidence 不備をエラー扱い

## 5. CI 統合

`pr-ci-status-comment.yml`（PR Maintenance / summarize）で以下を実施します。

1. Change Package 生成  
2. Change Package 検証  
3. commit 済み `artifacts/plan/plan-artifact.json` がある場合は schema validate
4. PR summary コメント本文へ Change Package / Plan Artifact セクションを追記
5. artifact としてアップロード

これにより、`pr-summary:detailed` の場合は証跡と再現コマンドを詳細表示し、digest の場合は短い要約を表示します。

auto-merge 運用と連携する場合:
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`（既定）で、PR summary 上の `Change Package Validation` が auto-merge eligibility 条件に含まれます。
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=0` にすると、validation 結果は `PASS` のみ許可されます。

## 6. 運用指針

- `risk:high` PR は Change Package の `missingRequiredLabels` / `exceptions` を優先確認する。  
- `risk:high` PR は実装前に `artifacts/plan/plan-artifact.json|md` を commit し、`policy-gate` の事前レビュー契約を満たす。
- `policy/risk-policy.yml` の更新時は、Change Package の判定結果が意図どおりかを fixture とテストで確認する。  
- schema 変更時は `fixtures/change-package/sample.change-package.json` と `scripts/ci/validate-json.mjs` の検証対象を同時更新する。  
- `change-package/v2` は preview 契約として扱い、v1 の既定運用を壊さない。dual-write / dual-validate は後続フェーズで導入する。
