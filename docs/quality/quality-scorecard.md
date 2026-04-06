---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-04-06'
---
# Quality Scorecard

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

`quality-scorecard/v1` is a read-only aggregation artifact that summarizes the health of recent summary artifacts and exposes a single decision/evidence view for PR and release review.

- canonical JSON: `artifacts/quality/quality-scorecard.json`
- canonical Markdown: `artifacts/quality/quality-scorecard.md`
- schema: `schema/quality-scorecard.schema.json`
- producer: `scripts/quality/build-quality-scorecard.mjs` / `pnpm run quality:scorecard:v1`
- validator: `scripts/ci/validate-quality-scorecard.mjs` / `pnpm run quality:scorecard:validate`

### 2. Inputs

#### 2.1 required

- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/report-envelope.json`

#### 2.2 optional

- `artifacts/assurance/assurance-summary.json`
- `artifacts/ci/harness-health.json`
- `artifacts/ci/policy-gate-summary.json`
- `artifacts/bench-compare.json`
- `artifacts/formal/formal-summary-v2.json`
- `artifacts/formal/formal-summary-v1.json` (fallback when v2 is absent)

The producer continues when optional artifacts are missing. Dimensions that depend on their own optional summaries, such as `assuranceCoverage`, `policyReadiness`, and `performanceRegression`, can become `missing`, while `executionHealth` still resolves to `pass` or `warn` when formal or harness inputs are absent. Missing required artifacts still trigger fail-fast behavior.

### 3. Evaluation dimensions

- `artifactIntegrity`
  - minimum presence and envelope consistency for required artifacts
- `assuranceCoverage`
  - claim count, warning claims, missing lane/evidence state, and counterexample state
- `executionHealth`
  - verify-lite step status, harness-health severity, and formal summary state
- `policyReadiness`
  - approvals, missing labels, policy errors, and warnings
- `performanceRegression`
  - overall benchmark candidate result from `bench-compare`

`summary.overallScore` is an auxiliary value. The operational source of truth remains `summary.overallStatus` and `blockers[]`.

### 4. Report-only rollout

- `verify-lite.yml` generates `quality-scorecard` in report-only mode.
- `validate-artifacts-ajv` and `validate-quality-scorecard.mjs` validate the schema.
- PR summary rendering shows `overallStatus`, `overallScore`, and `blockers`.
- Required branch-protection checks do not change because of this artifact.

### 5. Relationship with legacy `quality:scorecard`

The existing `quality:scorecard` entry in `package.json` still points to the legacy `scripts/quality-scorecard-generator.js` implementation. `quality-scorecard/v1` is introduced as a separate producer, validator, and artifact rather than as an in-place replacement.

### 6. Example commands

```bash
pnpm run quality:scorecard:v1 -- \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --report-envelope artifacts/report-envelope.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --formal-summary artifacts/formal/formal-summary-v2.json \
  --output-json artifacts/quality/quality-scorecard.json \
  --output-md artifacts/quality/quality-scorecard.md
```

```bash
pnpm run quality:scorecard:validate -- \
  artifacts/quality/quality-scorecard.json \
  schema/quality-scorecard.schema.json
```

---

## 日本語

### 1. 目的

`quality-scorecard/v1` は、既存の summary 成果物を read-only で横断集約し、PR / release 判断で「全体としてどの程度健全か」を 1 つの判断・証跡成果物として扱うための成果物です。

- 正規 JSON: `artifacts/quality/quality-scorecard.json`
- 正規 Markdown: `artifacts/quality/quality-scorecard.md`
- スキーマ: `schema/quality-scorecard.schema.json`
- 生成処理: `scripts/quality/build-quality-scorecard.mjs` / `pnpm run quality:scorecard:v1`
- 検証処理: `scripts/ci/validate-quality-scorecard.mjs` / `pnpm run quality:scorecard:validate`

### 2. 入力

#### 2.1 required

- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/report-envelope.json`

#### 2.2 optional

- `artifacts/assurance/assurance-summary.json`
- `artifacts/ci/harness-health.json`
- `artifacts/ci/policy-gate-summary.json`
- `artifacts/bench-compare.json`
- `artifacts/formal/formal-summary-v2.json`
- `artifacts/formal/formal-summary-v1.json`（v2 が無い場合の代替）

任意成果物が欠けていても生成処理は継続します。`assuranceCoverage` / `policyReadiness` / `performanceRegression` のように専用 summary に依存する評価次元は `missing` になり得ます。一方で formal summary や harness-health が無い場合でも `executionHealth` は `pass` / `warn` のまま評価されます。必須成果物が欠けた場合は即時失敗（fail-fast）します。

### 3. 評価次元

- `artifactIntegrity`
  - 必須成果物の存在と report envelope の最低限の整合性
- `assuranceCoverage`
  - claimCount / warningClaims / missing lane/evidence / counterexample の状態
- `executionHealth`
  - verify-lite step の状態、harness-health severity、formal summary の状態
- `policyReadiness`
  - approvals / missing labels / policy errors / warnings
- `performanceRegression`
  - `bench-compare` の candidate overall 結果

`summary.overallScore` は補助値であり、正とする判断値は `summary.overallStatus` と `blockers[]` です。

### 4. report-only 導入

- `verify-lite.yml` では report-only で `quality-scorecard` を生成します
- `validate-artifacts-ajv` と `validate-quality-scorecard.mjs` でスキーマを検証します
- PR summary には `overallStatus` / `overallScore` / `blockers` を表示します
- この成果物によって branch protection の required checks は変わりません

### 5. legacy `quality:scorecard` との関係

既存の `package.json` にある `quality:scorecard` は `scripts/quality-scorecard-generator.js` を呼ぶ legacy 実装です。  
`quality-scorecard/v1` は互換置換ではなく、別の生成処理 / 検証処理 / 成果物として導入します。

### 6. 実行例

```bash
pnpm run quality:scorecard:v1 -- \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --report-envelope artifacts/report-envelope.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --formal-summary artifacts/formal/formal-summary-v2.json \
  --output-json artifacts/quality/quality-scorecard.json \
  --output-md artifacts/quality/quality-scorecard.md
```

```bash
pnpm run quality:scorecard:validate -- \
  artifacts/quality/quality-scorecard.json \
  schema/quality-scorecard.schema.json
```
