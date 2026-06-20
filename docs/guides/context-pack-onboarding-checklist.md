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

### agent作業の事前確認
Context Pack は code generation の入力ファイルではなく、human / agent が共有する design SSOT です。Codex などの agent に実装変更を任せる前に、次を順番に確認します。

1. Issue本文の目的、target files、acceptance criteria、validation command
2. `AGENTS.md` の共通ルータと権限境界
3. `docs/spec/context-pack.md` と `spec/context-pack/boundary-map.json`
4. 対象sliceに紐づく acceptance tests / 既存テスト

変更が Context Pack の制約と矛盾する場合は、実装差分を作る前に Context Pack 更新または要求修正を判断し、PR または Issue comment に `Context Pack conflict: found` と矛盾する ID / pathを記録します。矛盾がない場合は `Context Pack conflict: none` を PR body に残します。通常変更は最小Context Pack + `pnpm -s run verify:lite` で開始し、traceability が必要な場合に Structured assurance、critical core のみ High-assurance lane へ昇格します。

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
- `traceability.status != success` または `traceability.missingCount > 0` の場合は、`artifacts/verify-lite/verify-lite-run-summary.json` の `traceability.matrixPath` を読み取り、その path を `--sources` に渡して strict traceability validation を再実行

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

### Agent-work preflight
Context Pack is the design SSOT shared by humans and agents, not a disposable code-generation input. Before assigning implementation work to Codex or another agent, inspect these inputs in order.

1. GitHub Issue objective, target files, acceptance criteria, and validation commands.
2. `AGENTS.md` for repository routing and permission boundaries.
3. `docs/spec/context-pack.md` and `spec/context-pack/boundary-map.json`.
4. Acceptance tests and existing tests tied to the affected slice.

If the requested change conflicts with Context Pack constraints, decide whether to update the Context Pack or revise the request before generating implementation changes, and record `Context Pack conflict: found` with the conflicting IDs/paths in the PR or Issue comment. If no conflict is found, record `Context Pack conflict: none` in the PR body. Start routine changes with a minimal Context Pack plus `pnpm -s run verify:lite`, add Structured assurance when traceability is needed, and promote only critical core slices to the High-assurance lane.

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

If `traceability.status != success` or `traceability.missingCount > 0`, read `traceability.matrixPath` from `artifacts/verify-lite/verify-lite-run-summary.json` (for example, `TRACEABILITY_MATRIX_PATH=$(jq -r '.traceability.matrixPath' artifacts/verify-lite/verify-lite-run-summary.json)`), then re-run strict traceability validation with that generated path:

```bash
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
