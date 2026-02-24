# Context Pack v1 Validation

> 🌍 Language / 言語: English | 日本語

---

## 日本語

Context Pack v1 は、AI/人間が更新する設計情報を SSOT として固定し、CI で機械検証するための入力契約です。

### 目的
- 設計仕様（objects / morphisms / diagrams / acceptance_tests など）を YAML/JSON で管理する
- `verify:lite` で schema 検証を必須化し、仕様破損を早期に検出する
- JSON/Markdown レポートを artifacts に出力し、失敗原因を追跡可能にする

### 配置ルール
- 既定の探索先: `spec/context-pack/**/*.{yml,yaml,json}`
- 例: `spec/context-pack/minimal-example.yaml`

### 実行コマンド
```bash
# 既定パスを検証
pnpm run context-pack:validate

# Objects/Morphisms と実装境界のマッピングを検証
pnpm run context-pack:verify-functor

# Natural Transformation（変更の意味保存）マッピングを検証
pnpm run context-pack:verify-natural-transformation

# Product/Coproduct（入力契約 + 失敗variant網羅）マッピングを検証
pnpm run context-pack:verify-product-coproduct

# 探索パス・出力先を上書き
node scripts/context-pack/validate.mjs \
  --sources 'spec/context-pack/**/*.{yml,yaml,json}' \
  --schema schema/context-pack-v1.schema.json \
  --report-json artifacts/context-pack/context-pack-validate-report.json \
  --report-md artifacts/context-pack/context-pack-validate-report.md

# Functorマッピングを直接検証（マップ・レポート先を上書き）
node scripts/context-pack/verify-functor.mjs \
  --map spec/context-pack/functor-map.json \
  --schema schema/context-pack-functor-map.schema.json \
  --report-json artifacts/context-pack/context-pack-functor-report.json \
  --report-md artifacts/context-pack/context-pack-functor-report.md

# Natural Transformationマッピングを直接検証（マップ・レポート先を上書き）
node scripts/context-pack/verify-natural-transformation.mjs \
  --map spec/context-pack/natural-transformations.json \
  --schema schema/context-pack-natural-transformation.schema.json \
  --report-json artifacts/context-pack/context-pack-natural-transformation-report.json \
  --report-md artifacts/context-pack/context-pack-natural-transformation-report.md

# Product/Coproductマッピングを直接検証（マップ・レポート先を上書き）
node scripts/context-pack/verify-product-coproduct.mjs \
  --map spec/context-pack/product-coproduct-map.json \
  --schema schema/context-pack-product-coproduct.schema.json \
  --report-json artifacts/context-pack/context-pack-product-coproduct-report.json \
  --report-md artifacts/context-pack/context-pack-product-coproduct-report.md

# Verify Lite でも必須ステップとして実行される
pnpm run verify:lite
```

### Functor 境界検証（Issue #2246）
- 入力:
  - `spec/context-pack/functor-map.json`（`schema/context-pack-functor-map.schema.json`）
  - `spec/context-pack/**/*.{yml,yaml,json}` の `objects[].id` / `morphisms[].id`
- 検査内容:
  - Context Pack ID と Functor map の対応漏れ・過不足を検出
  - `objects[].moduleGlobs` から実装境界を解決し、禁止依存・禁止ルール違反・循環依存を検出
  - `morphisms[].entrypoints` の `file` / `symbol` 存在を検証
- 失敗時:
  - `layer-violation` / `forbidden-import` / `object-dependency-cycle` / `morphism-entrypoint-missing-*` などの種別を JSON/Markdown レポートに出力

### Natural Transformation 検証（Issue #2247）
- 入力:
  - `spec/context-pack/natural-transformations.json`（`schema/context-pack-natural-transformation.schema.json`）
  - `spec/context-pack/**/*.{yml,yaml,json}` の `morphisms[].id` / `diagrams[].id` / `acceptance_tests[].id` / `forbidden_changes`
- 検査内容:
  - 変更種別テンプレート（`refactor` / `migration` / `breaking`）ごとの必須チェック
    - `refactor`: `regression`, `compatibility`
    - `migration`: `regression`, `compatibility`, `differential`
    - `breaking`: `regression`, `differential`
  - `before` / `after` 参照IDの存在確認（morphism/diagram/acceptance test）
  - `commutativityChecks` の証跡パス（ファイル or glob）存在確認
  - `entrypoints.file` / `entrypoints.symbol` の存在確認
  - `forbiddenChanges` と Context Pack `forbidden_changes` の整合
  - `breaking` 変更で `forbiddenChanges` 未連携の場合は fail
- 失敗時:
  - `transformation-reference-missing` / `commutativity-check-missing` / `commutativity-evidence-missing` /
    `forbidden-change-link-missing` / `forbidden-change-mismatch` / `transformation-entrypoint-missing-*`
    を JSON/Markdown レポートに出力

### Natural Transformation 記述例（最小）
```json
{
  "schemaVersion": "context-pack-natural-transformation/v1",
  "contextPackSources": ["spec/context-pack/**/*.{yml,yaml,json}"],
  "transformations": [
    {
      "id": "ReserveInventoryRefactor",
      "changeType": "refactor",
      "before": { "morphismIds": ["ReserveInventory"] },
      "after": { "morphismIds": ["ReserveInventory"] },
      "commutativityChecks": {
        "regression": ["tests/services/inventory-service.test.ts"],
        "compatibility": ["tests/api/reservations-routes.test.ts"],
        "differential": []
      }
    }
  ]
}
```

### Product/Coproduct 検証（Issue #2248）
- 入力:
  - `spec/context-pack/product-coproduct-map.json`（`schema/context-pack-product-coproduct.schema.json`）
  - `spec/context-pack/**/*.{yml,yaml,json}` の `morphisms[].input` / `morphisms[].failures`
- 検査内容:
  - Product（入力契約）:
    - `requiredInputKeys` が context-pack の `morphisms[].input` を完全にカバーしているか検証
    - `disallowGenericDtoKeys=true` の場合、`data` / `payload` / `body` / `dto` など曖昧DTOキーを拒否
  - Coproduct（失敗variant）:
    - `variants[].name` が context-pack の `morphisms[].failures` と一致しているか検証
    - `variants[].evidencePaths` が実在するファイル/グロブに解決できるか検証
  - variant coverage:
    - `coveredFailureVariants` / `uncoveredFailureVariants` をレポート出力
- 失敗時:
  - `product-required-input-missing` / `product-required-input-unknown` / `ambiguous-dto-key` /
    `coproduct-variant-missing` / `coproduct-variant-unknown` / `coproduct-evidence-missing`
    などの種別を JSON/Markdown レポートに出力

### Product/Coproduct 記述例（最小）
```json
{
  "schemaVersion": "context-pack-product-coproduct/v1",
  "contextPackSources": ["spec/context-pack/**/*.{yml,yaml,json}"],
  "products": [
    {
      "morphismId": "ReserveInventory",
      "requiredInputKeys": ["itemId", "quantity"],
      "disallowGenericDtoKeys": true
    }
  ],
  "coproducts": [
    {
      "morphismId": "ReserveInventory",
      "variants": [
        {
          "name": "OutOfStock",
          "evidencePaths": ["tests/services/inventory-service.test.ts"]
        }
      ]
    }
  ]
}
```

### 出力（artifacts）
- JSON: `artifacts/context-pack/context-pack-validate-report.json`
- Markdown: `artifacts/context-pack/context-pack-validate-report.md`
- JSON (Functor): `artifacts/context-pack/context-pack-functor-report.json`
- Markdown (Functor): `artifacts/context-pack/context-pack-functor-report.md`
- JSON (Natural Transformation): `artifacts/context-pack/context-pack-natural-transformation-report.json`
- Markdown (Natural Transformation): `artifacts/context-pack/context-pack-natural-transformation-report.md`
- JSON (Product/Coproduct): `artifacts/context-pack/context-pack-product-coproduct-report.json`
- Markdown (Product/Coproduct): `artifacts/context-pack/context-pack-product-coproduct-report.md`
- Verify Lite summary: `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackValidation`
  - `steps.contextPackFunctorValidation`
  - `steps.contextPackNaturalTransformationValidation`
  - `steps.contextPackProductCoproductValidation`
  - `artifacts.contextPackReportJson`
  - `artifacts.contextPackReportMarkdown`
  - `artifacts.contextPackFunctorReportJson`
  - `artifacts.contextPackFunctorReportMarkdown`
  - `artifacts.contextPackNaturalTransformationReportJson`
  - `artifacts.contextPackNaturalTransformationReportMarkdown`
  - `artifacts.contextPackProductCoproductReportJson`
  - `artifacts.contextPackProductCoproductReportMarkdown`

### よくある失敗
- `required` エラー: 必須キー不足（例: `domain_glossary.terms[].ja`）
- `type` エラー: 配列/オブジェクト/文字列の型不一致
- `parse` エラー: YAML 構文エラー、JSON 構文エラー
- `sources` エラー: 探索パターンに一致するファイルが 0 件
- `object/morphism mapping` エラー: Context Pack ID と Functor map の不一致
- `layer-violation` / `forbidden-import`: 境界/依存ルール違反
- `object-dependency-cycle`: object間依存の循環
- `morphism-entrypoint-missing-file/symbol`: 実装エントリポイントの欠落
- `commutativity-check-missing`: 変更種別に必須の可換チェック不足
- `commutativity-evidence-missing`: 回帰/互換/差分の証跡パス不足
- `forbidden-change-link-missing` / `forbidden-change-mismatch`: 禁止変更との連携不備
- `product-required-input-missing` / `product-required-input-unknown`: 必須入力の過不足
- `ambiguous-dto-key`: 曖昧DTOキーの使用
- `coproduct-variant-missing` / `coproduct-variant-unknown`: failure variant の過不足
- `coproduct-evidence-missing`: variant の証跡パス不足

### CI失敗時の復旧手順（Phase 3）
1. report を確認:
   - `artifacts/context-pack/context-pack-natural-transformation-report.json`
   - `artifacts/context-pack/context-pack-natural-transformation-report.md`
2. `spec/context-pack/natural-transformations.json` の以下を見直す:
   - `changeType` ごとの必須チェック充足（refactor/migration/breaking）
   - `before` / `after` の ID が Context Pack 本体に存在するか
   - `commutativityChecks` の証跡パスが実在するか（glob含む）
   - `breaking` 変更時に `forbiddenChanges` を連携しているか
3. ローカル再実行:
   - `pnpm run context-pack:verify-natural-transformation`
   - `pnpm run verify:lite`
4. report の `summary.totalViolations` が 0 であることを確認して再push

### CI失敗時の復旧手順（Phase 4）
1. report を確認:
   - `artifacts/context-pack/context-pack-product-coproduct-report.json`
   - `artifacts/context-pack/context-pack-product-coproduct-report.md`
2. `spec/context-pack/product-coproduct-map.json` の以下を見直す:
   - `products[].requiredInputKeys` が context-pack `morphisms[].input` を完全カバーしているか
   - `disallowGenericDtoKeys=true` 時に曖昧キー（data/payload/body/dtoなど）を使っていないか
   - `coproducts[].variants[].name` が `morphisms[].failures` と一致しているか
   - `coproducts[].variants[].evidencePaths` が実在するか
3. ローカル再実行:
   - `pnpm run context-pack:verify-product-coproduct`
   - `pnpm run verify:lite`
4. report の `uncoveredFailureVariants` と `summary.totalViolations` が 0 であることを確認して再push

---

## English

Context Pack v1 defines the SSOT input contract for design metadata and is validated in CI.

### Default source layout
- `spec/context-pack/**/*.{yml,yaml,json}`

### Commands
```bash
pnpm run context-pack:validate
pnpm run context-pack:verify-functor
pnpm run context-pack:verify-natural-transformation
pnpm run context-pack:verify-product-coproduct
pnpm run verify:lite
```

### Artifacts
- `artifacts/context-pack/context-pack-validate-report.json`
- `artifacts/context-pack/context-pack-validate-report.md`
- `artifacts/context-pack/context-pack-functor-report.json`
- `artifacts/context-pack/context-pack-functor-report.md`
- `artifacts/context-pack/context-pack-natural-transformation-report.json`
- `artifacts/context-pack/context-pack-natural-transformation-report.md`
- `artifacts/context-pack/context-pack-product-coproduct-report.json`
- `artifacts/context-pack/context-pack-product-coproduct-report.md`
- `artifacts/verify-lite/verify-lite-run-summary.json` (`steps.contextPackValidation`, `steps.contextPackFunctorValidation`, `steps.contextPackNaturalTransformationValidation`, `steps.contextPackProductCoproductValidation`)
