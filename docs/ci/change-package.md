---
docRole: ssot
lastVerified: '2026-05-08'
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

#### `change-package/v2` opt-in contract
- schema: `schema/change-package-v2.schema.json`
- sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- added sections:
  - `requirements`
  - `validationLanes`
  - `policyDecision`
  - `assurance`
  - `claims`
  - `assumptions`
  - `proofObligations`
  - `counterexamples`
  - `releaseControls`
  - `residualRisks`
  - `trustBoundary`
  - `runtimeControls`
  - `waivers`

The default path remains `change-package/v1`. v2 is available through opt-in generation, strict validation, and dual-write / dual-validate commands so migration can proceed without breaking existing consumers. The v2 package is the proof-carrying PR/release package: it preserves evidence-backed, waived, runtime-mitigated, unresolved, failed, and not-applicable claim states and points summaries to `artifacts/change-package/change-package-v2.json`.

### 3. Generation and validation commands
```bash
# Generate
node scripts/change-package/generate.mjs \
  --policy policy/risk-policy.yml \
  --output-json artifacts/change-package/change-package.json \
  --output-md artifacts/change-package/change-package.md

# Generate v2 explicitly
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --claim-level-summary artifacts/assurance/claim-level-summary.json

# Dual-write v1 + v2
node scripts/change-package/generate.mjs --dual-write

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

# Validate the v2 contract with strict artifactRefs / claim-reference checks
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

### 4. Main options
#### `generate.mjs`
- `--changed-files-file <path>`: explicit changed file list input
- `--event-path <path>`: GitHub event payload input
- `--artifact-root <path>`: artifact lookup root for evidence existence checks
- `--mode digest|detailed`: markdown output detail level
- `--schema-version v1|v2`: switch the generated contract; default is `v1`
- `--dual-write`: write v1 to `change-package.json|md` and v2 to `change-package-v2.json|md`
- `--claim-evidence-manifest`, `--policy-decision`, `--assurance-summary`, `--claim-level-summary`: optional v2 integration inputs
- `--post-deploy-verify <path>`: optional release/post-deploy verification input for v2 `releaseControls`

#### `validate.mjs`
- `--required-evidence <csv>`: explicit required evidence IDs
- `--strict`: treat required-evidence gaps as errors
- `--artifact-root <path>`: root used for v2 `artifactRefs` existence checks
- `--policy-decision <path>`: optional policy-decision/v1 consistency check for v2

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
- when `artifacts/change-package/change-package-v2.json` exists, PR summary rendering includes v2 claim / proof obligation / waiver counts, claim-state counts, and the evidence package path
- `AE_CHANGE_PACKAGE_DUAL_WRITE=1` enables opt-in v1 + v2 generation in the PR summary workflow; `AE_CHANGE_PACKAGE_V2_STRICT=1` makes its v2 validation strict

When tied to auto-merge:
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` includes Change Package Validation in auto-merge eligibility
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=0` requires `PASS` and rejects `WARN`

### 6. Operational guidance
- For `risk:high` PRs, review `missingRequiredLabels` and `exceptions` first
- For `risk:high` PRs, commit `artifacts/plan/plan-artifact.json|md` before implementation so `policy-gate` sees the pre-review contract
- When `policy/risk-policy.yml` changes, verify Change Package outcomes with fixtures and tests
- When the schema changes, update `fixtures/change-package/sample.change-package.json` and `scripts/ci/validate-json.mjs` together
- Keep `change-package/v1` as the default until downstream consumers explicitly migrate to v2
- Review `failed`, `not-applicable`, `runtime-mitigated`, and `waived` claim states explicitly; do not treat them as satisfied claims.
- For release decisions, review `releaseControls` and `residualRisks` in the v2 Markdown before relying on post-deploy mitigation.

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

### `change-package/v2`（opt-in contract）

- スキーマ: `schema/change-package-v2.schema.json`
- sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- 追加セクション:
  - `requirements`
  - `validationLanes`
  - `policyDecision`
  - `assurance`
  - `claims`
  - `assumptions`
  - `proofObligations`
  - `counterexamples`
  - `releaseControls`
  - `residualRisks`
  - `trustBoundary`
  - `runtimeControls`
  - `waivers`

既定経路は引き続き `change-package/v1` です。v2 は opt-in 生成、strict validation、dual-write / dual-validate による段階移行として利用できます。v2 は proof-carrying PR/release package であり、evidence-backed / waived / runtime-mitigated / unresolved / failed / not-applicable の claim state を区別し、summary から `artifacts/change-package/change-package-v2.json` を参照できるようにします。

## 3. 生成・検証コマンド

```bash
# 生成
node scripts/change-package/generate.mjs \
  --policy policy/risk-policy.yml \
  --output-json artifacts/change-package/change-package.json \
  --output-md artifacts/change-package/change-package.md

# v2 を明示生成
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --claim-level-summary artifacts/assurance/claim-level-summary.json

# v1 + v2 dual-write
node scripts/change-package/generate.mjs --dual-write

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

# v2 contract の strict validate（artifactRefs / claim reference / policy decision 整合性）
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

## 4. オプション（主なもの）

### `generate.mjs`
- `--changed-files-file <path>`: 変更ファイル一覧（改行区切り）を明示入力
- `--event-path <path>`: GitHub event payload の入力
- `--artifact-root <path>`: evidence 存在確認のルート
- `--mode digest|detailed`: Markdown 出力粒度
- `--schema-version v1|v2`: 生成する contract を切り替える。既定は `v1`
- `--dual-write`: v1 を `change-package.json|md`、v2 を `change-package-v2.json|md` に同時出力する
- `--claim-evidence-manifest`, `--policy-decision`, `--assurance-summary`, `--claim-level-summary`: v2 生成用の任意入力
- `--post-deploy-verify <path>`: v2 `releaseControls` に使う任意の release/post-deploy verification 入力

### `validate.mjs`
- `--required-evidence <csv>`: required evidence ID を明示
- `--strict`: required evidence 不備をエラー扱い
- `--artifact-root <path>`: v2 `artifactRefs` の実在確認ルート
- `--policy-decision <path>`: v2 と policy-decision/v1 の status / waiver 整合性確認

## 5. CI 統合

`pr-ci-status-comment.yml`（PR Maintenance / summarize）で以下を実施します。

1. Change Package 生成  
2. Change Package 検証  
3. commit 済み `artifacts/plan/plan-artifact.json` がある場合は schema validate
4. PR summary コメント本文へ Change Package / Plan Artifact セクションを追記
5. artifact としてアップロード

これにより、`pr-summary:detailed` の場合は証跡と再現コマンドを詳細表示し、digest の場合は短い要約を表示します。
`artifacts/change-package/change-package-v2.json` が存在する場合、PR summary は v2 の claims / proofObligations / waivers 件数、claim-state counts、evidence package path も表示します。
PR summary workflow では `AE_CHANGE_PACKAGE_DUAL_WRITE=1` で v1 + v2 生成を opt-in でき、`AE_CHANGE_PACKAGE_V2_STRICT=1` で v2 validation を strict にできます。

auto-merge 運用と連携する場合:
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`（既定）で、PR summary 上の `Change Package Validation` が auto-merge eligibility 条件に含まれます。
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=0` にすると、validation 結果は `PASS` のみ許可されます。

## 6. 運用指針

- `risk:high` PR は Change Package の `missingRequiredLabels` / `exceptions` を優先確認する。  
- `risk:high` PR は実装前に `artifacts/plan/plan-artifact.json|md` を commit し、`policy-gate` の事前レビュー契約を満たす。
- `policy/risk-policy.yml` の更新時は、Change Package の判定結果が意図どおりかを fixture とテストで確認する。  
- schema 変更時は `fixtures/change-package/sample.change-package.json` と `scripts/ci/validate-json.mjs` の検証対象を同時更新する。  
- downstream consumer が明示移行するまでは `change-package/v1` を既定運用として維持する。
- `failed`、`not-applicable`、`runtime-mitigated`、`waived` は satisfied claim として扱わず、明示的に確認する。
- release 判断では v2 Markdown の `releaseControls` と `residualRisks` を確認してから post-deploy mitigation に依存する。
