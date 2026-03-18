---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- schema/context-pack-v1.schema.json
lastVerified: '2026-03-18'
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

Minimal onboarding checklist for introducing Context Pack into a new project.

### Quick bootstrap
```bash
pnpm run context-pack:e2e-fixture
```

By default, reports are written to a temp directory and cleaned up on success (noise reduction).
Keep reports with:

```bash
CONTEXT_PACK_E2E_KEEP_REPORTS=1 pnpm run context-pack:e2e-fixture
# or
pnpm run context-pack:e2e-fixture -- --report-dir artifacts/context-pack-e2e
```

### Validation sequence
```bash
pnpm run context-pack:validate
pnpm run context-pack:validate -- --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}"
pnpm run context-pack:verify-functor
pnpm run context-pack:verify-natural-transformation
pnpm run context-pack:verify-product-coproduct
pnpm run context-pack:verify-boundary-map
pnpm run context-pack:verify-phase5
pnpm run context-pack:deps
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
pnpm run verify:lite
```

For incident recovery details, see `docs/spec/context-pack.md`.
