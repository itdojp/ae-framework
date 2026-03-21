---
docRole: ssot
lastVerified: '2026-03-21'
owner: context-pack-ops
verificationCommand: pnpm -s run check:doc-consistency
---
# Context Pack Troubleshooting Runbook

> 🌍 Language / 言語: English | 日本語

---

## 日本語

Context Pack 検証（`context-pack:*`, `verify:lite`）の失敗時に、診断と復旧を行う運用ランブックです。  
仕様契約は `docs/spec/context-pack.md`、実践例は `docs/guides/context-pack-phase5-cookbook.md` を参照してください。

### 前提条件
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- 検証対象: `spec/context-pack/**/*.{yml,yaml,json}`
- レポート: `artifacts/context-pack/` / `artifacts/verify-lite/`

### 共通診断フロー
1. 失敗した step を特定する（`verify:lite` summary または CI job log）
2. 対応する JSON/Markdown report を確認する
3. `context-pack-suggestions.{json,md}` で推奨修正（file/changeType/targetId）を確認する
4. report の `violations[].type` と対象 ID（object/morphism/diagram）を確認する
5. `spec/context-pack/*.json` または Context Pack 本体を修正する
6. 対象コマンドをローカル再実行する
7. `summary.totalViolations == 0` を確認して再 push する

### verify:lite で最初に見るファイル
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackValidation`
  - `steps.contextPackFunctorValidation`
  - `steps.contextPackNaturalTransformationValidation`
  - `steps.contextPackProductCoproductValidation`
  - `steps.contextPackPhase5Validation`
  - `steps.discoveryPackValidation`
  - `steps.discoveryPackCompile`
- `artifacts/context-pack/context-pack-suggestions.json`
- `artifacts/context-pack/context-pack-suggestions.md`

### フェーズ別復旧手順

#### 1) Base schema (`context-pack:validate`)
- report:
  - `artifacts/context-pack/context-pack-validate-report.json`
  - `artifacts/context-pack/context-pack-validate-report.md`
- 代表的な違反:
  - `required`, `type`, `parse`, `sources`
- 再実行:
```bash
pnpm run context-pack:validate
pnpm run verify:lite
```

#### 2) Functor (`context-pack:verify-functor`)
- report:
  - `artifacts/context-pack/context-pack-functor-report.json`
  - `artifacts/context-pack/context-pack-functor-report.md`
- 代表的な違反:
  - `object-mapping-missing`, `morphism-mapping-missing`
  - `layer-violation`, `forbidden-import`, `object-dependency-cycle`
  - `morphism-entrypoint-missing-file`, `morphism-entrypoint-missing-symbol`
- 再実行:
```bash
pnpm run context-pack:verify-functor
pnpm run verify:lite
```

#### 3) Natural Transformation (`context-pack:verify-natural-transformation`)
- report:
  - `artifacts/context-pack/context-pack-natural-transformation-report.json`
  - `artifacts/context-pack/context-pack-natural-transformation-report.md`
- 重点確認:
  - `changeType` ごとの必須可換性チェック
    - `refactor`: `regression` + `compatibility`
    - `migration`: `regression` + `compatibility` + `differential`
    - `breaking`: `regression` + `differential`
  - `before/after` の ID が Context Pack 本体に存在するか
  - `commutativityChecks` の証跡パスが実在するか
  - `breaking` 変更時の `forbiddenChanges` 連携
- 再実行:
```bash
pnpm run context-pack:verify-natural-transformation
pnpm run verify:lite
```

#### 4) Product/Coproduct (`context-pack:verify-product-coproduct`)
- report:
  - `artifacts/context-pack/context-pack-product-coproduct-report.json`
  - `artifacts/context-pack/context-pack-product-coproduct-report.md`
- 重点確認:
  - `products[].requiredInputKeys` が `morphisms[].input` を完全カバーしているか
  - `disallowGenericDtoKeys=true` で曖昧キー（`data/payload/body/dto`）を使っていないか
  - `variants[].name` が `morphisms[].failures` と一致しているか
  - `variants[].evidencePaths` が実在するか
- 再実行:
```bash
pnpm run context-pack:verify-product-coproduct
pnpm run verify:lite
```

#### 5) Phase5+ (`context-pack:verify-phase5`)
- report:
  - `artifacts/context-pack/context-pack-phase5-report.json`
  - `artifacts/context-pack/context-pack-phase5-report.md`
- 重点確認:
  - Pullback/Pushout の morphism/object/diagram 参照整合
  - Monoidal/Kleisli の境界整合（重複・欠落）
  - `evidencePaths` / `stringDiagramPaths` の実在
- 再実行:
```bash
pnpm run context-pack:verify-phase5
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
pnpm run verify:lite
```

#### 6) Boundary Map (`context-pack:verify-boundary-map`)
- report:
  - `artifacts/context-pack/context-pack-boundary-map-report.json`
  - `artifacts/context-pack/context-pack-boundary-map-report.md`
- 重点確認:
  - `slices[].produces` / `slices[].consumes` が Context Pack ref と一致しているか
  - `upstream.type=slice` の producer / target slice が実在するか
  - cycle が発生していないか
- 再実行:
```bash
pnpm run context-pack:verify-boundary-map
pnpm run verify:lite
```

#### 7) Dependency boundary (`context-pack:deps`)
- report:
  - `artifacts/context-pack/deps-summary.json`
  - `artifacts/context-pack/deps-summary.md`
- 重点確認:
  - `forbidden-import` / `layer-violation` / `object-dependency-cycle`
  - `strict=true` でのみ blocking になる前提か
  - `context-pack-suggestions.{json,md}` に `deps` 起点の修正提案が出ているか
- 再実行:
```bash
pnpm run context-pack:deps
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
pnpm run verify:lite
```

#### 8) Discovery upstream (`context-pack:validate -- --discovery-pack ...`)
- report:
  - `artifacts/context-pack/context-pack-validate-report.json`
  - `artifacts/context-pack/context-pack-validate-report.md`
- verify-lite で併せて確認するもの:
  - `artifacts/verify-lite/verify-lite-run-summary.json` の `steps.discoveryPackValidation` / `steps.discoveryPackCompile`
  - `artifacts/discovery-pack/discovery-pack-validate-report.json`
  - `artifacts/discovery-pack/discovery-pack-validate-report.md`
  - `artifacts/discovery-pack/discovery-pack-compile-report.json`
  - `artifacts/discovery-pack/discovery-pack-compile-report.md`
- 重点確認:
  - `upstream_refs` が Discovery Pack の `goal_ids` / `requirement_ids` / `business_use_case_ids` / `decision_ids` に解決できるか
  - approved Discovery 要素の未マップが warning 集計されていないか
  - `steps.discoveryPackValidation` / `steps.discoveryPackCompile` の notes に strict/report-only の理由が出ているか
- 再実行:
```bash
pnpm run context-pack:validate -- --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}"
pnpm run discovery-pack:validate
pnpm run discovery-pack:compile -- --target plan-spec --sources "spec/discovery-pack/**/*.{yml,yaml,json}"
pnpm run verify:lite
```

### エスカレーション基準
- 同一違反が 2 回以上再発する
- `parse`/`sources` が CI とローカルで再現条件不一致になる
- 依存規約（`forbidden-import`, `layer-violation`）で影響範囲が複数 object に波及する

上記の場合は、違反 report JSON と対象 PR/commit を添えて Issue 化することを推奨します。

---

## English

Operational runbook for diagnosing and recovering Context Pack validation failures in `context-pack:*` commands and `verify:lite`.
The normative contract lives in `docs/spec/context-pack.md`. The practical recipe set lives in `docs/guides/context-pack-phase5-cookbook.md`.

### Preconditions
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- Validation target: `spec/context-pack/**/*.{yml,yaml,json}`
- Reports: `artifacts/context-pack/` and `artifacts/verify-lite/`

### Common diagnostic flow
1. Identify the failed step from `verify:lite` summary or CI job logs.
2. Open the matching JSON/Markdown report.
3. Inspect `context-pack-suggestions.{json,md}` for recommended file/changeType/targetId edits.
4. Read `violations[].type` and the affected object/morphism/diagram IDs.
5. Fix the Context Pack source or the map file under `spec/context-pack/`.
6. Re-run the focused command locally.
7. Confirm `summary.totalViolations == 0` before pushing again.

### First files to inspect in `verify:lite`
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackValidation`
  - `steps.contextPackFunctorValidation`
  - `steps.contextPackNaturalTransformationValidation`
  - `steps.contextPackProductCoproductValidation`
  - `steps.contextPackPhase5Validation`
  - `steps.discoveryPackValidation`
  - `steps.discoveryPackCompile`
- `artifacts/context-pack/context-pack-suggestions.json`
- `artifacts/context-pack/context-pack-suggestions.md`

### Phased recovery procedure

#### 1) Base schema (`context-pack:validate`)
- Reports:
  - `artifacts/context-pack/context-pack-validate-report.json`
  - `artifacts/context-pack/context-pack-validate-report.md`
- Representative violations:
  - `required`, `type`, `parse`, `sources`
- Re-run:
```bash
pnpm run context-pack:validate
pnpm run verify:lite
```

#### 2) Functor (`context-pack:verify-functor`)
- Reports:
  - `artifacts/context-pack/context-pack-functor-report.json`
  - `artifacts/context-pack/context-pack-functor-report.md`
- Focus points:
  - `object-mapping-missing`, `morphism-mapping-missing`
  - `layer-violation`, `forbidden-import`, `object-dependency-cycle`
  - `morphism-entrypoint-missing-file`, `morphism-entrypoint-missing-symbol`
- Re-run:
```bash
pnpm run context-pack:verify-functor
pnpm run verify:lite
```

#### 3) Natural Transformation (`context-pack:verify-natural-transformation`)
- Reports:
  - `artifacts/context-pack/context-pack-natural-transformation-report.json`
  - `artifacts/context-pack/context-pack-natural-transformation-report.md`
- Focus points:
  - required commutativity checks by `changeType`
    - `refactor`: `regression` + `compatibility`
    - `migration`: `regression` + `compatibility` + `differential`
    - `breaking`: `regression` + `differential`
  - whether `before` / `after` IDs exist in the Context Pack
  - whether `commutativityChecks` evidence paths exist
  - whether `breaking` changes are linked to `forbiddenChanges`
- Re-run:
```bash
pnpm run context-pack:verify-natural-transformation
pnpm run verify:lite
```

#### 4) Product/Coproduct (`context-pack:verify-product-coproduct`)
- Reports:
  - `artifacts/context-pack/context-pack-product-coproduct-report.json`
  - `artifacts/context-pack/context-pack-product-coproduct-report.md`
- Focus points:
  - `products[].requiredInputKeys` completely cover `morphisms[].input`
  - `disallowGenericDtoKeys=true` does not leave ambiguous keys such as `data`, `payload`, `body`, `dto`
  - `variants[].name` matches `morphisms[].failures`
  - `variants[].evidencePaths` resolve to existing files/globs
- Re-run:
```bash
pnpm run context-pack:verify-product-coproduct
pnpm run verify:lite
```

#### 5) Phase5+ (`context-pack:verify-phase5`)
- Reports:
  - `artifacts/context-pack/context-pack-phase5-report.json`
  - `artifacts/context-pack/context-pack-phase5-report.md`
- Focus points:
  - Pullback/Pushout morphism/object/diagram references
  - Monoidal/Kleisli boundary consistency (overlap, missing refs)
  - `evidencePaths` / `stringDiagramPaths` existence
- Re-run:
```bash
pnpm run context-pack:verify-phase5
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
pnpm run verify:lite
```

#### 6) Boundary Map (`context-pack:verify-boundary-map`)
- Reports:
  - `artifacts/context-pack/context-pack-boundary-map-report.json`
  - `artifacts/context-pack/context-pack-boundary-map-report.md`
- Focus points:
  - `slices[].produces` / `slices[].consumes` match existing Context Pack refs
  - `upstream.type=slice` points to a real producer slice
  - slice graph does not contain cycles
- Re-run:
```bash
pnpm run context-pack:verify-boundary-map
pnpm run verify:lite
```

#### 7) Dependency boundary (`context-pack:deps`)
- Reports:
  - `artifacts/context-pack/deps-summary.json`
  - `artifacts/context-pack/deps-summary.md`
- Focus points:
  - `boundary-violation`, `dependency-cycle`
  - whether the failure is only blocking under `strict=true`
  - whether `context-pack-suggestions.{json,md}` already includes a dependency-oriented remediation proposal
- Re-run:
```bash
pnpm run context-pack:deps
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
pnpm run verify:lite
```

#### 8) Discovery upstream (`context-pack:validate -- --discovery-pack ...`)
- Reports:
  - `artifacts/context-pack/context-pack-validate-report.json`
  - `artifacts/context-pack/context-pack-validate-report.md`
- Also inspect in `verify:lite`:
  - `artifacts/verify-lite/verify-lite-run-summary.json` for `steps.discoveryPackValidation` / `steps.discoveryPackCompile`
  - `artifacts/discovery-pack/discovery-pack-validate-report.json`
  - `artifacts/discovery-pack/discovery-pack-validate-report.md`
  - `artifacts/discovery-pack/discovery-pack-compile-report.json`
  - `artifacts/discovery-pack/discovery-pack-compile-report.md`
- Focus points:
  - whether `upstream_refs` resolve to Discovery Pack `goal_ids`, `requirement_ids`, `business_use_case_ids`, or `decision_ids`
  - whether approved Discovery items are still reported as unmapped warnings
  - whether `steps.discoveryPackValidation` / `steps.discoveryPackCompile` notes explain strict vs report-only behavior
- Re-run:
```bash
pnpm run context-pack:validate -- --discovery-pack "spec/discovery-pack/**/*.{yml,yaml,json}"
pnpm run discovery-pack:validate
pnpm run discovery-pack:compile -- --target plan-spec --sources "spec/discovery-pack/**/*.{yml,yaml,json}"
pnpm run verify:lite
```

### Escalation criteria
- The same violation reappears two or more times.
- `parse` / `sources` failures do not reproduce consistently between CI and local runs.
- Dependency policy violations (`forbidden-import`, `layer-violation`) propagate across multiple objects.

When that happens, open an Issue with the violation report JSON and the affected PR/commit attached.
