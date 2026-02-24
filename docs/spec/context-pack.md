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

# 探索パス・出力先を上書き
node scripts/context-pack/validate.mjs \
  --sources 'spec/context-pack/**/*.{yml,yaml,json}' \
  --schema schema/context-pack-v1.schema.json \
  --report-json artifacts/context-pack/context-pack-validate-report.json \
  --report-md artifacts/context-pack/context-pack-validate-report.md

# Verify Lite でも必須ステップとして実行される
pnpm run verify:lite
```

### 出力（artifacts）
- JSON: `artifacts/context-pack/context-pack-validate-report.json`
- Markdown: `artifacts/context-pack/context-pack-validate-report.md`
- Verify Lite summary: `artifacts/verify-lite/verify-lite-run-summary.json`
  - `steps.contextPackValidation`
  - `artifacts.contextPackReportJson`
  - `artifacts.contextPackReportMarkdown`

### よくある失敗
- `required` エラー: 必須キー不足（例: `domain_glossary.terms[].ja`）
- `type` エラー: 配列/オブジェクト/文字列の型不一致
- `parse` エラー: YAML 構文エラー、JSON 構文エラー
- `sources` エラー: 探索パターンに一致するファイルが 0 件

---

## English

Context Pack v1 defines the SSOT input contract for design metadata and is validated in CI.

### Default source layout
- `spec/context-pack/**/*.{yml,yaml,json}`

### Commands
```bash
pnpm run context-pack:validate
pnpm run verify:lite
```

### Artifacts
- `artifacts/context-pack/context-pack-validate-report.json`
- `artifacts/context-pack/context-pack-validate-report.md`
- `artifacts/verify-lite/verify-lite-run-summary.json` (`steps.contextPackValidation`)
