---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- schema/context-pack-v1.schema.json
lastVerified: '2026-03-27'
---
# Context Pack Onboarding Checklist

> 🌍 Language / 言語: English | 日本語

---

## 日本語

Context Pack を新規プロジェクトへ導入する際の最小チェックリストです。  
入力準備 → 検証 → 修正 → 再検証のループを標準化します。

### 前提条件
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- 実行場所: repository root

### 0. 最小E2E fixture でツール疎通を確認
まず framework 側の最小 fixture を実行して、ローカル環境と validator の疎通を確認します。

```bash
pnpm run context-pack:e2e-fixture
```

補足:
- 既定では report は一時ディレクトリに出力され、成功時に自動削除されます（差分ノイズ抑制）。
- report を保持したい場合:

```bash
CONTEXT_PACK_E2E_KEEP_REPORTS=1 pnpm run context-pack:e2e-fixture
# または
pnpm run context-pack:e2e-fixture -- --report-dir artifacts/context-pack-e2e
```

### 1. 入力ファイルを準備
- Context Pack 本体: `spec/context-pack/**/*.{yml,yaml,json}`
- Discovery Pack（`upstream_refs` を使う場合）: `spec/discovery-pack/**/*.{yml,yaml,json}`
- Functor map: `spec/context-pack/functor-map.json`
- Natural Transformation map: `spec/context-pack/natural-transformations.json`
- Product/Coproduct map: `spec/context-pack/product-coproduct-map.json`
- Boundary Map: `spec/context-pack/boundary-map.json`
- Phase5 templates: `spec/context-pack/phase5-templates.json`

### 2. 個別検証を実行
```bash
pnpm run context-pack:validate
# upstream_refs を使う場合
pnpm run context-pack:validate -- --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}"
pnpm run context-pack:verify-functor
pnpm run context-pack:verify-natural-transformation
pnpm run context-pack:verify-product-coproduct
pnpm run context-pack:verify-boundary-map
pnpm run context-pack:verify-phase5
pnpm run context-pack:deps
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
```

### 3. 統合検証（verify-lite）
```bash
pnpm run verify:lite
```

確認対象:
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
- `traceability.status != success` または `traceability.missingCount > 0` の場合は `ae validate --traceability --strict --sources <traceability.matrixPath>` を再実行

### 4. 失敗時の修正ループ
1. 対応する report JSON/Markdown を確認
2. `violations[].type` と対象ID（object/morphism/diagram）を修正
3. 対象コマンドと `verify:lite` を再実行
4. `summary.totalViolations == 0` を確認

障害対応の詳細は `docs/spec/context-pack.md` を参照してください。

### 5. PR前確認
- [ ] Context Pack 系 8 コマンドが成功
- [ ] `context-pack-suggestions.{json,md}` で `recommendedContextChanges` を確認済み
- [ ] `upstream_refs` を使う場合、`--discovery-pack` 付き validate で Discovery Pack 整合を確認済み
- [ ] `verify:lite` で Context Pack 関連 step が想定通り
- [ ] `verify:lite` の top-level `traceability.status=success` と `missingCount=0` を確認済み
- [ ] assurance を導入する場合、`assurance.profile` / `claim_refs` を設定し `docs/guides/assurance-onboarding-checklist.md` を実施済み
- [ ] report に不要な差分ノイズを持ち込んでいない
- [ ] `evidencePaths` が stale path ではない

---

## English

Minimal onboarding checklist for introducing Context Pack into a new project. The goal is to standardize the loop of input preparation -> validation -> repair -> re-validation.

### Prerequisites
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- Run from the repository root

### 0. Confirm tool wiring with the minimal end-to-end fixture
Start with the framework-owned minimal fixture to verify the local environment and validators before touching project-specific inputs.

```bash
pnpm run context-pack:e2e-fixture
```

Notes:
- By default, reports are written to a temp directory and removed on success to reduce diff noise.
- Keep reports when you need to inspect the generated artifacts:

```bash
CONTEXT_PACK_E2E_KEEP_REPORTS=1 pnpm run context-pack:e2e-fixture
# or
pnpm run context-pack:e2e-fixture -- --report-dir artifacts/context-pack-e2e
```

### 1. Prepare input files
- Context Pack source: `spec/context-pack/**/*.{yml,yaml,json}`
- Discovery Pack source when `upstream_refs` is used: `spec/discovery-pack/**/*.{yml,yaml,json}`
- Functor map: `spec/context-pack/functor-map.json`
- Natural transformation map: `spec/context-pack/natural-transformations.json`
- Product/Coproduct map: `spec/context-pack/product-coproduct-map.json`
- Boundary map: `spec/context-pack/boundary-map.json`
- Phase5 templates: `spec/context-pack/phase5-templates.json`

### 2. Run focused validators
```bash
pnpm run context-pack:validate
# when upstream_refs is used
pnpm run context-pack:validate -- --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}"
pnpm run context-pack:verify-functor
pnpm run context-pack:verify-natural-transformation
pnpm run context-pack:verify-product-coproduct
pnpm run context-pack:verify-boundary-map
pnpm run context-pack:verify-phase5
pnpm run context-pack:deps
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
```

### 3. Run integrated verification (`verify-lite`)
```bash
pnpm run verify:lite
```

Check the following in `artifacts/verify-lite/verify-lite-run-summary.json`:
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

If `traceability.status != success` or `traceability.missingCount > 0`, re-run strict traceability validation with the generated matrix path:

```bash
TRACEABILITY_MATRIX_PATH=artifacts/traceability/issue-requirements-matrix.json
ae validate --traceability --strict --sources "$TRACEABILITY_MATRIX_PATH"
```

### 4. Repair loop when a step fails
1. Open the matching JSON / Markdown report.
2. Fix `violations[].type` and the referenced object / morphism / diagram IDs.
3. Re-run the focused validator and then `pnpm run verify:lite`.
4. Confirm `summary.totalViolations == 0`.

For deeper troubleshooting, see `docs/spec/context-pack.md`.

### 5. Pre-PR checklist
- [ ] All eight Context Pack commands succeed.
- [ ] `context-pack-suggestions.{json,md}` has been reviewed for `recommendedContextChanges`.
- [ ] If `upstream_refs` is used, validation with `--discovery-pack` confirms Discovery Pack alignment.
- [ ] `verify:lite` shows the expected Context Pack-related steps.
- [ ] `verify:lite` top-level `traceability.status=success` and `missingCount=0` are confirmed.
- [ ] If assurance is enabled, `assurance.profile` / `claim_refs` are configured and `docs/guides/assurance-onboarding-checklist.md` has been completed.
- [ ] No unnecessary report noise is being introduced.
- [ ] `evidencePaths` does not contain stale paths.
