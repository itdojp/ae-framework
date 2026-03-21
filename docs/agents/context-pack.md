---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/guides/context-pack-onboarding-checklist.md
- docs/guides/upstream-context-promotion.md
- docs/operations/context-pack-troubleshooting.md
lastVerified: '2026-03-21'
---

# Agents Runbook: Context Pack

## When to use

### 日本語
- Context Pack の構造検証や Phase5+ 検証を実行するとき
- `upstream_refs` を使う Context Pack と Discovery Pack の整合を確認するとき
- Boundary Map / 依存境界 / verify-lite の失敗を復旧するとき

### English
- Run Context Pack structure validation or Phase5+ validation.
- Check the consistency between Context Pack and Discovery Pack when `upstream_refs` are present.
- Recover from Boundary Map, dependency boundary, or `verify:lite` failures.

## What to load (primary sources)

### 日本語
- `docs/spec/context-pack.md`
- `docs/guides/context-pack-onboarding-checklist.md`
- `docs/guides/upstream-context-promotion.md`
- `docs/operations/context-pack-troubleshooting.md`

### English
- `docs/spec/context-pack.md`
- `docs/guides/context-pack-onboarding-checklist.md`
- `docs/guides/upstream-context-promotion.md`
- `docs/operations/context-pack-troubleshooting.md`

## Commands (copy/paste)

The commands below are the current operator baseline. Use the focused validator first, then re-run `verify:lite`.

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

## Artifacts to check

### 日本語
- `artifacts/context-pack/context-pack-phase5-report.{json,md}`
- `artifacts/context-pack/context-pack-validate-report.{json,md}`
- `artifacts/context-pack/context-pack-functor-report.{json,md}`
- `artifacts/context-pack/context-pack-natural-transformation-report.{json,md}`
- `artifacts/context-pack/context-pack-product-coproduct-report.{json,md}`
- `artifacts/context-pack/context-pack-boundary-map-report.{json,md}`
- `artifacts/context-pack/deps-summary.{json,md}`
- `artifacts/context-pack/context-pack-suggestions.{json,md}`
- `artifacts/verify-lite/verify-lite-run-summary.json`
- CI の `context-pack-e2e` / `verify-lite` / context-pack 関連ジョブ結果

### English
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

## verify-lite で最初に見る項目

### 日本語
- `artifacts/verify-lite/verify-lite-run-summary.json`
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
- `steps.discoveryPackValidation` / `steps.discoveryPackCompile` は verify-lite 側の実行記録です。`context-pack:validate -- --discovery-pack ...` 単独実行では Discovery Pack validate / compile report は生成されません。
- Context Pack validate 単独の primary report は `artifacts/context-pack/context-pack-validate-report.{json,md}` です。
- `traceability` は top-level summary です。`status != success` または `missingCount > 0` の場合は `matrixPath` と `notes` を起点に `ae validate --traceability --strict --sources <matrixPath>` を再実行してください。

### English
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

## Escalation / follow-up

### 日本語
- モデル境界の修正が必要な場合は、対象 spec と生成物を同時に更新
- 自動修復系（suggest/patch）検討は #2290 の方針に従う

### English
- When model boundaries change, update the target spec and generated artifacts in the same change set.
- Follow the policy in `#2290` before introducing automated remediation flows such as suggest/patch.
