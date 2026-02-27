# Change Package (証跡パッケージ)

> Language / 言語: English | 日本語

---

## English (Summary)

Change Package standardizes PR safety evidence into machine-readable artifacts:

- `artifacts/change-package/change-package.json`
- `artifacts/change-package/change-package.md`
- `artifacts/change-package/change-package-validation.json`
- `artifacts/change-package/change-package-validation.md`

Primary components:
- Generator: `scripts/change-package/generate.mjs`
- Validator: `scripts/change-package/validate.mjs`
- Schema: `schema/change-package.schema.json`
- Sample fixture: `fixtures/change-package/sample.change-package.json`

---

## 日本語

## 1. 目的

PR の安全性判断を diff 中心ではなく、証跡（evidence）中心で扱うための標準成果物です。  
`policy/risk-policy.yml` と変更差分を入力に、リスク判定・必要ラベル・再現コマンド・監視計画を機械可読で出力します。

## 2. 出力物

- `artifacts/change-package/change-package.json`
  - スキーマ: `change-package/v1`
  - 主要項目:
    - `intent`: 変更意図
    - `scope`: 変更ファイル数・対象領域
    - `risk`: selected / inferred / required labels / 根拠
    - `evidence`: verify-lite / policy-gate / harness-health などの存在確認
    - `reproducibility`: 再現コマンド
    - `rolloutPlan`, `monitoringPlan`, `exceptions`
- `artifacts/change-package/change-package.md`
  - PR サマリに貼り込む人間向け要約
- `artifacts/change-package/change-package-validation.json|md`
  - schema 検証と required evidence 判定の結果

## 3. 生成・検証コマンド

```bash
# 生成
node scripts/change-package/generate.mjs \
  --policy policy/risk-policy.yml \
  --output-json artifacts/change-package/change-package.json \
  --output-md artifacts/change-package/change-package.md

# 検証（非strict: missing evidence は warning）
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package.json \
  --schema schema/change-package.schema.json

# 検証（strict: missing evidence で fail）
node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package.json \
  --schema schema/change-package.schema.json \
  --required-evidence verifyLiteSummary,policyGateSummary \
  --strict
```

## 4. オプション（主なもの）

### `generate.mjs`
- `--changed-files-file <path>`: 変更ファイル一覧（改行区切り）を明示入力
- `--event-path <path>`: GitHub event payload の入力
- `--artifact-root <path>`: evidence 存在確認のルート
- `--mode digest|detailed`: Markdown 出力粒度

### `validate.mjs`
- `--required-evidence <csv>`: required evidence ID を明示
- `--strict`: required evidence 不備をエラー扱い

## 5. CI 統合

`pr-ci-status-comment.yml`（PR Maintenance / summarize）で以下を実施します。

1. Change Package 生成  
2. Change Package 検証  
3. PR summary コメント本文へ Change Package セクションを追記  
4. artifact としてアップロード  

これにより、`pr-summary:detailed` の場合は証跡と再現コマンドを詳細表示し、digest の場合は短い要約を表示します。

auto-merge 運用と連携する場合:
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`（既定）で、PR summary 上の `Change Package Validation` が auto-merge eligibility 条件に含まれます。
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=0` にすると、validation 結果は `PASS` のみ許可されます。

## 6. 運用指針

- `risk:high` PR は Change Package の `missingRequiredLabels` / `exceptions` を優先確認する。  
- `policy/risk-policy.yml` の更新時は、Change Package の判定結果が意図どおりかを fixture とテストで確認する。  
- schema 変更時は `fixtures/change-package/sample.change-package.json` と `scripts/ci/validate-json.mjs` の検証対象を同時更新する。  
