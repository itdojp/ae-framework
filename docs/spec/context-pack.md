---
docRole: ssot
lastVerified: '2026-03-18'
owner: context-pack-ops
verificationCommand: pnpm -s run check:doc-consistency
---
# Context Pack v1 Validation

> 🌍 Language / 言語: English | 日本語

---

## 日本語

Context Pack v1 は、AI/人間が更新する設計情報を SSOT として固定し、CI で機械検証するための入力契約です。

### 目的
- 設計仕様（objects / morphisms / diagrams / acceptance_tests など）を YAML/JSON で管理する
- `verify:lite` で schema 検証を必須化し、仕様破損を早期に検出する
- JSON/Markdown レポートを artifacts に出力し、失敗原因を追跡可能にする

### 関連ドキュメント
- 実践手順（Phase5+ cookbook）: `docs/guides/context-pack-phase5-cookbook.md`
- 障害対応（CI/ローカル復旧）: `docs/operations/context-pack-troubleshooting.md`
- 仕様配置レジストリ: `docs/spec/registry.md`
- Discovery Pack 昇格規律ガイド: `docs/guides/upstream-context-promotion.md`

### 配置ルール
- 既定の探索先: `spec/context-pack/**/*.{yml,yaml,json}`
- 例: `spec/context-pack/minimal-example.yaml`

### assurance profile 参照（Phase 1）
- `context-pack-v1` では optional `assurance` セクションを持てます。
- 用途は「この Context Pack がどの assurance profile / claim を参照するか」を固定することです。
- 現時点では schema validation、report-only `verify:assurance` summary、Verify Lite での report-only 収集、`enforce-assurance` ラベル時の strict assurance enforcement までが実装済みです。通常時は report-only ですが、strict step は `policy/risk-policy.yml` に従って label-gated で有効化されます。

```yaml
assurance:
  profile: inventory-baseline-v1
  claim_refs:
    - no-negative-stock
```

- `profile`: `schema/assurance-profile.schema.json` の `profileId`
- `claim_refs`: assurance profile の `claims[].id`
- `claim_refs` は assurance aggregate が spec-derived evidence を claim に配賦するためのアンカーにもなります。
- 詳細: `docs/quality/assurance-profile.md`, `docs/quality/assurance-lanes.md`

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

# Slice-level produces/consumes 境界を検証
pnpm run context-pack:verify-boundary-map

# Phase5+（Pullback/Pushout・Monoidal・Kleisli）テンプレを検証
pnpm run context-pack:verify-phase5

# 依存境界（層の方向・循環依存）を検証
pnpm run context-pack:deps

# violation report から修正提案を生成
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack

# 探索パス・出力先を上書き
node scripts/context-pack/validate.mjs \
  --sources 'spec/context-pack/**/*.{yml,yaml,json}' \
  --schema schema/context-pack-v1.schema.json \
  --report-json artifacts/context-pack/context-pack-validate-report.json \
  --report-md artifacts/context-pack/context-pack-validate-report.md \
  --discovery-pack 'spec/discovery-pack/**/*.{yml,yaml,json}'

# Discovery Pack まで trace を延長する場合の最小例
node scripts/context-pack/validate.mjs \
  --sources 'spec/context-pack/**/*.{yml,yaml,json}' \
  --discovery-pack 'spec/discovery-pack/**/*.{yml,yaml,json}'

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

# Boundary Map を直接検証（マップ・レポート先を上書き）
node scripts/context-pack/verify-boundary-map.mjs \
  --map spec/context-pack/boundary-map.json \
  --schema schema/context-pack-boundary-map.schema.json \
  --report-json artifacts/context-pack/context-pack-boundary-map-report.json \
  --report-md artifacts/context-pack/context-pack-boundary-map-report.md

# Phase5+テンプレを直接検証（マップ・レポート先を上書き）
node scripts/context-pack/verify-phase5-templates.mjs \
  --map spec/context-pack/phase5-templates.json \
  --schema schema/context-pack-phase5-templates.schema.json \
  --report-json artifacts/context-pack/context-pack-phase5-report.json \
  --report-md artifacts/context-pack/context-pack-phase5-report.md

# 依存境界検証を直接実行（strict は label gating と連動）
node scripts/context-pack/check-deps.mjs \
  --rules configs/context-pack/dependency-rules.json \
  --strict false \
  --report-json artifacts/context-pack/deps-summary.json \
  --report-md artifacts/context-pack/deps-summary.md

# 既存 report から修正提案を生成（Harness Health の recommendedContextChanges と連携）
node scripts/context-pack/suggest.mjs \
  --report-dir artifacts/context-pack \
  --report-json artifacts/context-pack/context-pack-suggestions.json \
  --report-md artifacts/context-pack/context-pack-suggestions.md

# assurance summary を report-only 生成
node scripts/assurance/aggregate-lanes.mjs \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --context-pack fixtures/context-pack/sample.context-pack.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md

# Verify Lite では report-only で収集される
# （required artifact gate には含めない）

# strict assurance enforcement をローカル再現
# Verify Lite の strict step は `enforce-assurance` label で有効化される
node scripts/ci/enforce-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json
```

### Discovery Pack upstream（optional）
- pack-level:
  - `upstream.discovery_pack.path`
  - `upstream.discovery_pack.profile`
- element-level:
  - `morphisms[].upstream_refs`
  - `acceptance_tests[].upstream_refs`
  - `diagrams[].upstream_refs`（任意）
- `upstream_refs` の対象:
  - `goal_ids`
  - `requirement_ids`
  - `business_use_case_ids`
  - `decision_ids`
- validate に `--discovery-pack` を渡すと、Context Pack 側の `upstream_refs` と Discovery Pack ID の整合を検証し、approved Discovery 要素の未マップも warning として集計します。

### 依存境界ルール検証（Issue #2278）
- ルール定義: `configs/context-pack/dependency-rules.json`
- 既定ルール（最小）:
  - `src/core/**` -> `src/agents/**` を禁止
  - `src/mcp-server/**` -> `scripts/**` を禁止
  - `src/**` -> `docs/**` を禁止
  - `src/*` モジュール単位の循環依存を禁止
- 出力:
  - `artifacts/context-pack/deps-summary.json`
  - `artifacts/context-pack/deps-summary.md`
- CI 連動:
  - `context-pack-quality-gate.yml` で常に実行
  - `enforce-context-pack` ラベル（または strict dispatch/main 設定）時は blocking

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

### counterexample -> suggestion の戻し先
- `counterexample.schema.json` の `suggestedContextChanges.contextPackSuggestionPath` は、`context-pack/suggest.mjs` が生成する suggestion artifact への戻し先として利用できます。
- `claim_refs` は、counterexample の `claimIds` と合わせて claim 単位の triage loop を固定するためのアンカーです。

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

### Boundary Map 検証（Issue #2648）
- 入力:
  - `spec/context-pack/boundary-map.json`（`schema/context-pack-boundary-map.schema.json`）
  - `spec/context-pack/**/*.{yml,yaml,json}` の `objects[].id` / `morphisms[].id` / `diagrams[].id` / `acceptance_tests[].id` / `forbidden_changes`
- 検査内容:
  - `slices[].produces` / `slices[].consumes` が既存 Context Pack ref と整合しているか検証
  - `consumes[].upstream.type=slice` の場合、参照先 slice が実在し、対象 ref を実際に produce しているか検証
  - 同一 `kind/refId` を複数 slice が produce していないか検証
  - slice 間依存グラフの循環を検出
- 失敗時:
  - `boundary-ref-missing`
  - `boundary-upstream-slice-missing`
  - `boundary-upstream-producer-missing`
  - `boundary-producer-duplicate`
  - `boundary-slice-cycle`
  などの種別を JSON/Markdown レポートに出力

### Boundary Map 記述例（最小）
```json
{
  "schemaVersion": "context-pack-boundary-map/v1",
  "contextPackSources": ["spec/context-pack/**/*.{yml,yaml,json}"],
  "slices": [
    {
      "id": "inventory-item-model",
      "produces": [
        {
          "kind": "object",
          "refId": "InventoryItem"
        }
      ]
    },
    {
      "id": "reservation-flow",
      "consumes": [
        {
          "kind": "object",
          "refId": "InventoryItem",
          "upstream": {
            "type": "slice",
            "sliceId": "inventory-item-model"
          }
        }
      ],
      "produces": [
        {
          "kind": "morphism",
          "refId": "ReserveInventory"
        }
      ]
    }
  ]
}
```

### Phase 5+ テンプレ検証（Issue #2252）
- 入力:
  - `spec/context-pack/phase5-templates.json`（`schema/context-pack-phase5-templates.schema.json`）
  - `spec/context-pack/**/*.{yml,yaml,json}` の `objects[].id` / `morphisms[].id` / `diagrams[].id`
- 検査内容:
  - Pullback/Pushout:
    - morphism/object/diagram 参照IDの存在確認
    - `evidencePaths` の実在確認（file/glob）
    - template ID 重複検出
  - Monoidal:
    - `parallelMorphismIds` / `mergeMorphismId` の存在確認
    - `tensorLawChecks[].evidencePaths` / `stringDiagramPaths` の証跡確認
  - Kleisli:
    - `morphismIds` の存在確認
    - `pureBoundaryMorphismIds` / `impureBoundaryMorphismIds` の境界整合（重複禁止、参照漏れ禁止、impure空禁止）
    - `bindEvidencePaths` / `sideEffectEvidencePaths` の証跡確認
- 失敗時:
  - `pullback-morphism-missing` / `pushout-object-missing` / `monoidal-morphism-missing` /
    `kleisli-boundary-overlap` / `kleisli-impure-boundary-missing` / `phase5-evidence-missing`
    などの種別を JSON/Markdown レポートに出力

### Phase 5+ 記述例（最小）
```json
{
  "schemaVersion": "context-pack-phase5-templates/v1",
  "contextPackSources": ["spec/context-pack/**/*.{yml,yaml,json}"],
  "pullbacks": [
    {
      "id": "ReserveReleasePullback",
      "leftMorphismId": "ReserveInventory",
      "rightMorphismId": "ReleaseInventory",
      "apexObjectId": "InventoryItem",
      "commutingDiagramIds": ["D-1"],
      "evidencePaths": ["tests/services/inventory-service.test.ts"]
    }
  ],
  "pushouts": [],
  "monoidalFlows": [],
  "kleisliPipelines": [
    {
      "id": "ReservationEffectPipeline",
      "effectType": "io",
      "morphismIds": ["ReserveInventory"],
      "pureBoundaryMorphismIds": [],
      "impureBoundaryMorphismIds": ["ReserveInventory"],
      "bindEvidencePaths": ["tests/services/inventory-service.test.ts"],
      "sideEffectEvidencePaths": ["src/domain/services.ts"]
    }
  ]
}
```

### 出力（artifacts）
- JSON: `artifacts/context-pack/context-pack-validate-report.json`
- Markdown: `artifacts/context-pack/context-pack-validate-report.md`
- `--discovery-pack` を指定した場合、validate report は `warnings` に
  - `upstream-refs-missing`
  - `unmapped-approved-requirement`
  - `unmapped-approved-business-use-case`
  - `discovery-pack-profile-mismatch`
  を追加し、`errors` に
  - `discovery-pack-source-missing`
  - `discovery-pack-source-ambiguous`
  - `upstream-ref-missing`
  を追加します
- JSON (Dependency boundary): `artifacts/context-pack/deps-summary.json`
- Markdown (Dependency boundary): `artifacts/context-pack/deps-summary.md`
- JSON (Suggestions): `artifacts/context-pack/context-pack-suggestions.json`
- Markdown (Suggestions): `artifacts/context-pack/context-pack-suggestions.md`
- JSON (Functor): `artifacts/context-pack/context-pack-functor-report.json`
- Markdown (Functor): `artifacts/context-pack/context-pack-functor-report.md`
- JSON (Natural Transformation): `artifacts/context-pack/context-pack-natural-transformation-report.json`
- Markdown (Natural Transformation): `artifacts/context-pack/context-pack-natural-transformation-report.md`
- JSON (Product/Coproduct): `artifacts/context-pack/context-pack-product-coproduct-report.json`
- Markdown (Product/Coproduct): `artifacts/context-pack/context-pack-product-coproduct-report.md`
- JSON (Boundary Map): `artifacts/context-pack/context-pack-boundary-map-report.json`
- Markdown (Boundary Map): `artifacts/context-pack/context-pack-boundary-map-report.md`
- JSON (Phase5+): `artifacts/context-pack/context-pack-phase5-report.json`
- Markdown (Phase5+): `artifacts/context-pack/context-pack-phase5-report.md`
- Verify Lite summary: `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackValidation`
  - `steps.contextPackFunctorValidation`
  - `steps.contextPackNaturalTransformationValidation`
  - `steps.contextPackProductCoproductValidation`
  - `steps.contextPackPhase5Validation`
  - `steps.discoveryPackValidation`
  - `steps.discoveryPackCompile`
  - top-level `discoveryPack`
  - `artifacts.contextPackReportJson`
  - `artifacts.contextPackReportMarkdown`
  - `artifacts.contextPackFunctorReportJson`
  - `artifacts.contextPackFunctorReportMarkdown`
  - `artifacts.contextPackNaturalTransformationReportJson`
  - `artifacts.contextPackNaturalTransformationReportMarkdown`
  - `artifacts.contextPackProductCoproductReportJson`
  - `artifacts.contextPackProductCoproductReportMarkdown`
  - `artifacts.contextPackPhase5ReportJson`
  - `artifacts.contextPackPhase5ReportMarkdown`
  - `artifacts.discoveryPackValidateReportJson`
  - `artifacts.discoveryPackValidateReportMarkdown`
  - `artifacts.discoveryPackCompileReportJson`
  - `artifacts.discoveryPackCompileReportMarkdown`
  - `artifacts.discoveryPackPlanSpec`

### よくある失敗
- `required` エラー: 必須キー不足（例: `domain_glossary.terms[].ja`）
- `type` エラー: 配列/オブジェクト/文字列の型不一致
- `parse` エラー: YAML 構文エラー、JSON 構文エラー
- `sources` エラー: 探索パターンに一致するファイルが 0 件
- `object/morphism mapping` エラー: Context Pack ID と Functor map の不一致
- `layer-violation` / `forbidden-import`: 境界/依存ルール違反
- `object-dependency-cycle`: object間依存の循環
- `boundary-violation` / `dependency-cycle`: `context-pack:deps` の境界/循環違反
- `morphism-entrypoint-missing-file/symbol`: 実装エントリポイントの欠落
- `commutativity-check-missing`: 変更種別に必須の可換チェック不足
- `commutativity-evidence-missing`: 回帰/互換/差分の証跡パス不足
- `forbidden-change-link-missing` / `forbidden-change-mismatch`: 禁止変更との連携不備
- `product-required-input-missing` / `product-required-input-unknown`: 必須入力の過不足
- `ambiguous-dto-key`: 曖昧DTOキーの使用
- `coproduct-variant-missing` / `coproduct-variant-unknown`: failure variant の過不足
- `coproduct-evidence-missing`: variant の証跡パス不足
- `boundary-ref-missing`: Context Pack ref 未定義
- `boundary-upstream-slice-missing` / `boundary-upstream-producer-missing`: upstream produce/consume 不整合
- `boundary-producer-duplicate` / `boundary-slice-cycle`: slice 境界定義の重複・循環
- `discovery-pack-source-missing` / `discovery-pack-source-ambiguous`: Discovery Pack upstream の解決失敗
- `upstream-ref-missing`: `upstream_refs` が Discovery Pack ID を参照できない
- `upstream-refs-missing`: `morphisms` / `acceptance_tests` の `upstream_refs` 欠落
- `unmapped-approved-requirement` / `unmapped-approved-business-use-case`: approved Discovery 要素の未マップ
- `discovery-pack-profile-mismatch`: Context Pack 宣言 profile と Discovery Pack 実体の不一致
- `*-template-duplicate`: Phase5+ テンプレ ID 重複
- `kleisli-boundary-overlap` / `kleisli-impure-boundary-missing`: Kleisli 境界不整合
- `phase5-evidence-missing`: Phase5+ 証跡パス不足

### 運用時の診断・復旧
CI失敗時の詳細な診断フロー（Phase 3/4/5+）は `docs/operations/context-pack-troubleshooting.md` を参照してください。
本ドキュメントは入力契約と違反種別の定義を正として扱います。

---

## English

Context Pack v1 defines the SSOT input contract for design metadata and is validated in CI.

### Related docs
- Practical recipes (Phase5+): `docs/guides/context-pack-phase5-cookbook.md`
- Troubleshooting (CI/local recovery): `docs/operations/context-pack-troubleshooting.md`
- Spec registry: `docs/spec/registry.md`

### Default source layout
- `spec/context-pack/**/*.{yml,yaml,json}`

### Commands
```bash
pnpm run context-pack:validate
pnpm run context-pack:verify-functor
pnpm run context-pack:verify-natural-transformation
pnpm run context-pack:verify-product-coproduct
pnpm run context-pack:verify-boundary-map
pnpm run context-pack:verify-phase5
pnpm run context-pack:deps
node scripts/context-pack/suggest.mjs --report-dir artifacts/context-pack
pnpm run verify:lite
```

### Artifacts
- `artifacts/context-pack/context-pack-validate-report.json`
- `artifacts/context-pack/context-pack-validate-report.md`
- `artifacts/context-pack/deps-summary.json`
- `artifacts/context-pack/deps-summary.md`
- `artifacts/context-pack/context-pack-suggestions.json`
- `artifacts/context-pack/context-pack-suggestions.md`
- `artifacts/context-pack/context-pack-functor-report.json`
- `artifacts/context-pack/context-pack-functor-report.md`
- `artifacts/context-pack/context-pack-natural-transformation-report.json`
- `artifacts/context-pack/context-pack-natural-transformation-report.md`
- `artifacts/context-pack/context-pack-product-coproduct-report.json`
- `artifacts/context-pack/context-pack-product-coproduct-report.md`
- `artifacts/context-pack/context-pack-boundary-map-report.json`
- `artifacts/context-pack/context-pack-boundary-map-report.md`
- `artifacts/context-pack/context-pack-phase5-report.json`
- `artifacts/context-pack/context-pack-phase5-report.md`
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackValidation`
  - `steps.contextPackFunctorValidation`
  - `steps.contextPackNaturalTransformationValidation`
  - `steps.contextPackProductCoproductValidation`
  - `steps.contextPackPhase5Validation`
  - `steps.discoveryPackValidation`
  - `steps.discoveryPackCompile`
  - top-level `discoveryPack`
  - `artifacts.discoveryPackValidateReportJson`
  - `artifacts.discoveryPackValidateReportMarkdown`
  - `artifacts.discoveryPackCompileReportJson`
  - `artifacts.discoveryPackCompileReportMarkdown`
  - `artifacts.discoveryPackPlanSpec`
