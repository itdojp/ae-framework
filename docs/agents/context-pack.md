---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/guides/context-pack-onboarding-checklist.md
- docs/guides/upstream-context-promotion.md
- docs/operations/context-pack-troubleshooting.md
lastVerified: '2026-03-31'
---

# Agents Runbook: Context Pack

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need to run Context Pack structure validation or Phase5+ validation
- when you need to verify consistency between Context Pack and Discovery Pack while `upstream_refs` are present
- when you need to recover from Boundary Map, dependency boundary, or `verify:lite` failures

### What to load (primary sources)
- `docs/spec/context-pack.md`
- `docs/guides/context-pack-onboarding-checklist.md`
- `docs/guides/upstream-context-promotion.md`
- `docs/operations/context-pack-troubleshooting.md`

### Commands (copy/paste)
The commands below are the current operator baseline. Start with the focused validator, then re-run `verify:lite`.

```bash
pnpm -s run context-pack:validate
```

```bash
pnpm -s run context-pack:validate -- --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}"
```

```bash
pnpm -s run context-pack:verify-functor
```

```bash
pnpm -s run context-pack:verify-natural-transformation
```

```bash
pnpm -s run context-pack:verify-product-coproduct
```

```bash
pnpm -s run context-pack:verify-boundary-map
```

```bash
pnpm -s run context-pack:verify-phase5
```

```bash
pnpm -s run context-pack:deps
```

```bash
pnpm -s run context-pack:e2e-fixture
```

```bash
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
```

```bash
pnpm -s run verify:lite
```

### Artifacts to check
- `artifacts/context-pack/context-pack-phase5-report.{json,md}`
- `artifacts/context-pack/context-pack-validate-report.{json,md}`
- `artifacts/context-pack/context-pack-functor-report.{json,md}`
- `artifacts/context-pack/context-pack-natural-transformation-report.{json,md}`
- `artifacts/context-pack/context-pack-product-coproduct-report.{json,md}`
- `artifacts/context-pack/context-pack-boundary-map-report.{json,md}`
- `artifacts/context-pack/deps-summary.{json,md}`
- `artifacts/context-pack/context-pack-suggestions.{json,md}`
- `artifacts/verify-lite/verify-lite-run-summary.json`
- CI job results for `context-pack-e2e`, `verify-lite`, and the Context Pack validators

### First verify-lite fields to inspect
- Start from `artifacts/verify-lite/verify-lite-run-summary.json` and inspect:
  - `steps.contextPackValidation`
  - `steps.contextPackFunctorValidation`
  - `steps.contextPackNaturalTransformationValidation`
  - `steps.contextPackProductCoproductValidation`
  - `steps.contextPackPhase5Validation`
  - `steps.discoveryPackValidation`
  - `steps.discoveryPackCompile`
  - top-level `traceability.status`
  - top-level `traceability.missingCount`
  - top-level `traceability.matrixPath`
  - top-level `traceability.notes`
- `steps.discoveryPackValidation` and `steps.discoveryPackCompile` are execution records from `verify-lite`. Running only `context-pack:validate -- --discovery-pack ...` does not generate Discovery Pack validate/compile reports.
- The primary report for standalone Context Pack validate is `artifacts/context-pack/context-pack-validate-report.{json,md}`.
- `traceability` is a top-level summary. If `status != success` or `missingCount > 0`, re-run `ae validate --traceability --strict --sources <matrixPath>` from `matrixPath` and `notes`.

### Escalation / follow-up
- when model boundaries change, update the target spec and generated artifacts in the same change set
- follow the policy in `#2290` before introducing automated remediation flows such as suggest/patch

## 日本語

### When to use
- Context Pack の構造検証や Phase5+ 検証を実行するとき
- `upstream_refs` を使う Context Pack と Discovery Pack の整合を確認するとき
- Boundary Map / 依存境界 / `verify:lite` の失敗を復旧するとき

### What to load (primary sources)
- `docs/spec/context-pack.md`
- `docs/guides/context-pack-onboarding-checklist.md`
- `docs/guides/upstream-context-promotion.md`
- `docs/operations/context-pack-troubleshooting.md`

### Commands (copy/paste)
以下は current operator baseline です。まず focused validator を実行し、その後で `verify:lite` を再実行します。

```bash
pnpm -s run context-pack:validate
```

```bash
pnpm -s run context-pack:validate -- --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}"
```

```bash
pnpm -s run context-pack:verify-functor
```

```bash
pnpm -s run context-pack:verify-natural-transformation
```

```bash
pnpm -s run context-pack:verify-product-coproduct
```

```bash
pnpm -s run context-pack:verify-boundary-map
```

```bash
pnpm -s run context-pack:verify-phase5
```

```bash
pnpm -s run context-pack:deps
```

```bash
pnpm -s run context-pack:e2e-fixture
```

```bash
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
```

```bash
pnpm -s run verify:lite
```

### Artifacts to check
- `artifacts/context-pack/context-pack-phase5-report.{json,md}`
- `artifacts/context-pack/context-pack-validate-report.{json,md}`
- `artifacts/context-pack/context-pack-functor-report.{json,md}`
- `artifacts/context-pack/context-pack-natural-transformation-report.{json,md}`
- `artifacts/context-pack/context-pack-product-coproduct-report.{json,md}`
- `artifacts/context-pack/context-pack-boundary-map-report.{json,md}`
- `artifacts/context-pack/deps-summary.{json,md}`
- `artifacts/context-pack/context-pack-suggestions.{json,md}`
- `artifacts/verify-lite/verify-lite-run-summary.json`
- CI の `context-pack-e2e` / `verify-lite` / Context Pack validator 関連 job 結果

### verify-lite で最初に見る項目
- `artifacts/verify-lite/verify-lite-run-summary.json` から以下を確認する
  - `steps.contextPackValidation`
  - `steps.contextPackFunctorValidation`
  - `steps.contextPackNaturalTransformationValidation`
  - `steps.contextPackProductCoproductValidation`
  - `steps.contextPackPhase5Validation`
  - `steps.discoveryPackValidation`
  - `steps.discoveryPackCompile`
  - top-level `traceability.status`
  - top-level `traceability.missingCount`
  - top-level `traceability.matrixPath`
  - top-level `traceability.notes`
- `steps.discoveryPackValidation` / `steps.discoveryPackCompile` は `verify-lite` の実行記録です。`context-pack:validate -- --discovery-pack ...` 単独実行では Discovery Pack validate / compile report は生成されません。
- Context Pack validate 単独の primary report は `artifacts/context-pack/context-pack-validate-report.{json,md}` です。
- `traceability` は top-level summary です。`status != success` または `missingCount > 0` の場合は、`matrixPath` と `notes` を起点に `ae validate --traceability --strict --sources <matrixPath>` を再実行してください。

### Escalation / follow-up
- モデル境界の修正が必要な場合は、対象 spec と生成物を同時に更新する
- suggest / patch のような自動 remediation flow を導入する前に、`#2290` の方針に従う
