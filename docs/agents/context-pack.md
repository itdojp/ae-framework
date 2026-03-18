---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/guides/context-pack-onboarding-checklist.md
- docs/guides/upstream-context-promotion.md
- docs/operations/context-pack-troubleshooting.md
lastVerified: '2026-03-18'
---

# Agents Runbook: Context Pack

## When to use

- Context Pack の構造検証や Phase5+ 検証を実行するとき
- `upstream_refs` を使う Context Pack と Discovery Pack の整合を確認するとき
- Boundary Map / 依存境界 / verify-lite の失敗を復旧するとき

## What to load (primary sources)

- `docs/spec/context-pack.md`
- `docs/guides/context-pack-onboarding-checklist.md`
- `docs/guides/upstream-context-promotion.md`
- `docs/operations/context-pack-troubleshooting.md`

## Commands (copy/paste)

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

## verify-lite で最初に見る項目

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
- `traceability` は top-level summary です。`status != success` の場合は `matrixPath` と `notes` を起点に `ae validate --traceability --strict` を再実行してください。

## Escalation / follow-up

- モデル境界の修正が必要な場合は、対象specと生成物を同時に更新
- 自動修復系（suggest/patch）検討は #2290 の方針に従う
