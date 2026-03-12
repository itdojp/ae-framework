---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-03-12'
---
# Quality Scorecard

> Language / 言語: English | 日本語

---

## English (Summary)

`quality-scorecard/v1` is a report-only aggregation artifact that summarizes the current state of verify-lite, assurance, policy, harness, benchmark, and formal summaries without changing branch protection.

---

## 日本語

## 1. 目的

`quality-scorecard/v1` は、既存の summary artifact を read-only で横断集約し、PR / release 判断で「全体としてどの程度健全か」を 1 つの decision/evidence artifact として扱うための成果物です。

- canonical JSON: `artifacts/quality/quality-scorecard.json`
- canonical Markdown: `artifacts/quality/quality-scorecard.md`
- schema: `schema/quality-scorecard.schema.json`
- producer: `scripts/quality/build-quality-scorecard.mjs` / `pnpm run quality:scorecard:v1`
- validator: `scripts/ci/validate-quality-scorecard.mjs` / `pnpm run quality:scorecard:validate`

## 2. 入力

### 2.1 required

- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/report-envelope.json`

### 2.2 optional

- `artifacts/assurance/assurance-summary.json`
- `artifacts/ci/harness-health.json`
- `artifacts/ci/policy-gate-summary.json`
- `artifacts/bench-compare.json`
- `artifacts/formal/formal-summary-v2.json`
- `artifacts/formal/formal-summary-v1.json`（v2 が無い場合の fallback）

optional artifact が欠けていても producer は継続し、対応する dimension は `missing` として扱います。required artifact が欠けた場合は producer が fail-fast します。

## 3. 評価次元

- `artifactIntegrity`
  - required artifact の存在と report envelope の最低限の整合
- `assuranceCoverage`
  - claimCount / warningClaims / missing lane/evidence / counterexample 状態
- `executionHealth`
  - verify-lite step 状態、harness-health severity、formal summary 状態
- `policyReadiness`
  - approvals / missing labels / policy errors / warnings
- `performanceRegression`
  - `bench-compare` の candidate overall

`summary.overallScore` は補助値であり、source of truth は `summary.overallStatus` と `blockers[]` です。

## 4. report-only 導入

- `verify-lite.yml` では report-only で `quality-scorecard` を生成します
- `validate-artifacts-ajv` と `validate-quality-scorecard.mjs` で schema を検証します
- PR summary には `overallStatus` / `overallScore` / `blockers` を表示します
- branch protection の required checks 自体は変更しません

## 5. legacy `quality:scorecard` との関係

既存の `package.json` にある `quality:scorecard` は `scripts/quality-scorecard-generator.js` を呼ぶ legacy 実装です。  
`quality-scorecard/v1` は互換置換ではなく、別 producer / validator / artifact として導入します。

## 6. 実行例

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
