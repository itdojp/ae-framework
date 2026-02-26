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

### エスカレーション基準
- 同一違反が 2 回以上再発する
- `parse`/`sources` が CI とローカルで再現条件不一致になる
- 依存規約（`forbidden-import`, `layer-violation`）で影響範囲が複数 object に波及する

上記の場合は、違反 report JSON と対象 PR/commit を添えて Issue 化することを推奨します。

---

## English

Operational runbook for diagnosing and recovering Context Pack validation failures.

### Quick flow
1. Identify the failed step (`verify:lite` summary or CI logs).
2. Inspect matching JSON/Markdown reports under `artifacts/context-pack/`.
3. Check `context-pack-suggestions.{json,md}` for actionable changes.
4. Fix IDs/evidence/schema fields in `spec/context-pack/`.
5. Re-run the target command and `pnpm run verify:lite`.
6. Confirm `summary.totalViolations == 0` before re-push.

### Typical reports
- Base: `context-pack-validate-report.{json,md}`
- Functor: `context-pack-functor-report.{json,md}`
- Natural Transformation: `context-pack-natural-transformation-report.{json,md}`
- Product/Coproduct: `context-pack-product-coproduct-report.{json,md}`
- Phase5+: `context-pack-phase5-report.{json,md}`

### Commands
```bash
pnpm run context-pack:validate
pnpm run context-pack:verify-functor
pnpm run context-pack:verify-natural-transformation
pnpm run context-pack:verify-product-coproduct
pnpm run context-pack:verify-phase5
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
pnpm run verify:lite
```
