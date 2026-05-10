---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-05-09'
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

### 5. Canonical route and legacy `quality:scorecard` compatibility

For new PR and release evidence, the canonical route is `quality-scorecard/v1`: `scripts/quality/build-quality-scorecard.mjs`, `pnpm run quality:scorecard:v1`, and `pnpm run quality:scorecard:validate`. The existing `quality:scorecard` entry in `package.json` still points to the compatibility script `scripts/quality-scorecard-generator.js`. Without the required v1 inputs it preserves the legacy diagnostic route and writes `./quality-scorecard.md`; when callers provide both required v1 inputs (`--verify-lite-summary` and `--report-envelope`) it delegates to the canonical v1 producer and can write `artifacts/quality/quality-scorecard.json` / `.md`. Optional v1 flags such as `--output-json` / `--output-md` do not trigger delegation by themselves. Operators can force the legacy diagnostic route with `--legacy` or `--legacy-diagnostic`. Treat the legacy diagnostic output as compatibility-only, not as the canonical PR/release judgment artifact.

Do not remove the legacy no-input behavior until the remaining workflow and operator consumers are migrated. The tested migration path is to pass the v1 inputs through the compatibility script or call `quality:scorecard:v1` directly. The route matrix in `docs/reference/ASSURANCE-CANONICAL-ROUTES.md` is the cleanup reference.

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

Compatibility wrapper example for existing `quality:scorecard` callers that are ready to supply v1 inputs:

```bash
pnpm run quality:scorecard -- \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --report-envelope artifacts/report-envelope.json \
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

`quality-scorecard/v1` は、既存の summary 成果物を読み取り専用（read-only）で横断集約し、PR / release 判断で「全体としてどの程度健全か」を 1 つの判断・証跡成果物として扱うための成果物です。

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

任意成果物が欠けていても生成処理は継続します。`assuranceCoverage` / `policyReadiness` / `performanceRegression` のように専用の summary 成果物に依存する評価次元は `missing` になり得ます。一方で formal summary や harness-health が無い場合でも `executionHealth` は `pass` / `warn` のまま評価されます。必須成果物が欠けた場合は即時失敗（fail-fast）します。

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

### 4. 報告専用（report-only）導入

- `verify-lite.yml` では報告専用（report-only）で `quality-scorecard` を生成します
- `validate-artifacts-ajv` と `validate-quality-scorecard.mjs` でスキーマを検証します
- PR summary には `overallStatus` / `overallScore` / `blockers` を表示します
- この成果物によって branch protection の required checks は変わりません

### 5. 正準導線と legacy `quality:scorecard` 互換

新しい PR / release evidence では、`quality-scorecard/v1` を正準導線として扱います。該当する実装は `scripts/quality/build-quality-scorecard.mjs`、`pnpm run quality:scorecard:v1`、`pnpm run quality:scorecard:validate` です。既存の `package.json` にある `quality:scorecard` は互換 script の `scripts/quality-scorecard-generator.js` を呼びます。v1 入力を渡さない場合は legacy diagnostic route として `./quality-scorecard.md` を生成し、必須 v1 入力（`--verify-lite-summary` と `--report-envelope`）を渡した場合は正準 v1 producer に委譲して `artifacts/quality/quality-scorecard.json` / `.md` を生成できます。入力なし legacy diagnostic output は互換専用であり、正準の PR / release judgment artifact ではありません。

legacy の入力なし挙動は、残存 workflow / operator consumer が移行されるまで削除しません。test 済みの移行導線は、互換 script に v1 入力を渡すか、`quality:scorecard:v1` を直接呼ぶことです。cleanup の参照先は `docs/reference/ASSURANCE-CANONICAL-ROUTES.md` です。

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

既存の `quality:scorecard` 呼び出し側が v1 入力を渡せる場合の互換 wrapper 例:

```bash
pnpm run quality:scorecard -- \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --report-envelope artifacts/report-envelope.json \
  --output-json artifacts/quality/quality-scorecard.json \
  --output-md artifacts/quality/quality-scorecard.md
```

```bash
pnpm run quality:scorecard:validate -- \
  artifacts/quality/quality-scorecard.json \
  schema/quality-scorecard.schema.json
```
