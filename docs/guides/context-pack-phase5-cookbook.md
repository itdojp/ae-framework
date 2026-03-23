---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- schema/context-pack-phase5-templates.schema.json
lastVerified: '2026-03-23'
---
# Context Pack Phase5+ Cookbook

> 🌍 Language / 言語: English | 日本語

---

## 日本語

本ドキュメントは、Context Pack Phase5+（Pullback/Pushout・Monoidal・Kleisli）の実践例をまとめた運用ガイドです。  
仕様定義と契約の参照は `docs/spec/context-pack.md`、障害対応は `docs/operations/context-pack-troubleshooting.md` を使用してください。

### 前提条件
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- Context Pack本体: `spec/context-pack/**/*.{yml,yaml,json}`
- Phase5 map: `spec/context-pack/phase5-templates.json`

### Recipe 1: Pullback/Pushout の統合チェック
1. `spec/context-pack/phase5-templates.json` に Pullback/Pushout を記述する
2. morphism/object/diagram の ID が Context Pack 本体に存在することを確認する
3. 証跡 `evidencePaths` が実在することを確認する
4. 検証を実行する

```bash
pnpm run context-pack:verify-phase5
```

期待結果:
- `artifacts/context-pack/context-pack-phase5-report.json`
- `artifacts/context-pack/context-pack-phase5-report.md`
- `summary.totalViolations == 0`

### Recipe 2: Monoidal（並列分業）チェック
1. `monoidalFlows[].parallelMorphismIds` に並列処理morphismを列挙する
2. `mergeMorphismId` に合流morphismを指定する
3. `tensorLawChecks[].evidencePaths` と `stringDiagramPaths` を設定する
4. 検証を実行する

```bash
pnpm run context-pack:verify-phase5
```

注意:
- `parallelMorphismIds` の重複は `monoidal-parallel-morphism-duplicate` で失敗する
- 証跡不足は `phase5-evidence-missing` で失敗する

### Recipe 3: Kleisli（pure/impure境界）チェック
1. `kleisliPipelines[].morphismIds` を定義する
2. `pureBoundaryMorphismIds` / `impureBoundaryMorphismIds` を定義する
3. 少なくとも1つの impure 境界を設定する
4. 検証を実行する

```bash
pnpm run context-pack:verify-phase5
```

注意:
- pure/impure 重複は `kleisli-boundary-overlap`
- impure 未設定は `kleisli-impure-boundary-missing`
- boundary が morphismIds 外を参照すると `kleisli-boundary-reference-missing`

### verify-lite 連携確認
```bash
pnpm run verify:lite
```

確認ポイント:
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackPhase5Validation`
  - `artifacts.contextPackPhase5ReportJson`
  - `artifacts.contextPackPhase5ReportMarkdown`

### PR前チェックリスト
- [ ] `pnpm run context-pack:verify-phase5` が成功する
- [ ] `pnpm run verify:lite` で `contextPackPhase5Validation` が意図通りの状態になる
- [ ] `context-pack-phase5-report.json` の違反件数を確認済み
- [ ] `evidencePaths` が stale path になっていない

---

## English

This guide documents the current operational recipes for Context Pack Phase5+ templates (Pullback/Pushout, Monoidal, and Kleisli).
Use `docs/spec/context-pack.md` for the normative contract and schema details, and use `docs/operations/context-pack-troubleshooting.md` when a validator run fails in CI or local verification.

### Prerequisites
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- Context Pack source: `spec/context-pack/**/*.{yml,yaml,json}`
- Phase5 map: `spec/context-pack/phase5-templates.json`

### Recipe 1: Pullback/Pushout integration check
1. Define Pullback or Pushout entries in `spec/context-pack/phase5-templates.json`.
2. Confirm that every referenced morphism, object, and diagram ID exists in the primary Context Pack sources.
3. Confirm that every `evidencePaths` entry resolves to a tracked file.
4. Run the validator.

```bash
pnpm run context-pack:verify-phase5
```

Expected outputs:
- `artifacts/context-pack/context-pack-phase5-report.json`
- `artifacts/context-pack/context-pack-phase5-report.md`
- `summary.totalViolations == 0`

### Recipe 2: Monoidal parallel-flow check
1. Populate `monoidalFlows[].parallelMorphismIds` with the morphisms that may execute in parallel.
2. Set `mergeMorphismId` to the morphism that rejoins the branch.
3. Provide `tensorLawChecks[].evidencePaths` and `stringDiagramPaths`.
4. Run the validator.

```bash
pnpm run context-pack:verify-phase5
```

Operational notes:
- Duplicate `parallelMorphismIds` fail with `monoidal-parallel-morphism-duplicate`.
- Missing evidence paths fail with `phase5-evidence-missing`.

### Recipe 3: Kleisli pure/impure boundary check
1. Define `kleisliPipelines[].morphismIds`.
2. Define `pureBoundaryMorphismIds` and `impureBoundaryMorphismIds`.
3. Provide at least one impure boundary.
4. Run the validator.

```bash
pnpm run context-pack:verify-phase5
```

Operational notes:
- Overlap between pure and impure sets fails with `kleisli-boundary-overlap`.
- Missing impure boundaries fail with `kleisli-impure-boundary-missing`.
- Boundaries that reference morphisms outside `morphismIds` fail with `kleisli-boundary-reference-missing`.

### Verify Lite integration check
```bash
pnpm run verify:lite
```

Review the following fields first:
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackPhase5Validation`
  - `artifacts.contextPackPhase5ReportJson`
  - `artifacts.contextPackPhase5ReportMarkdown`

### Pre-PR checklist
- [ ] `pnpm run context-pack:verify-phase5` succeeds locally
- [ ] `pnpm run verify:lite` reports the expected `contextPackPhase5Validation` status
- [ ] `context-pack-phase5-report.json` was reviewed for residual violations
- [ ] `evidencePaths` do not point to stale or renamed files
