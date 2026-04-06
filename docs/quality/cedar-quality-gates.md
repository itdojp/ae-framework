---
docRole: derived
canonicalSource:
- policy/quality.json
- docs/quality/verification-gates.md
lastVerified: '2026-04-06'
---
# Cedar Policies Quality Gates (report-only)

> 🌍 Language / 言語: English | 日本語

---

## English

This workflow scans `policies/cedar/` for `.json` (Cedar JSON) and `.cedar` / `.ced` files and produces a non-blocking summary.

### Current behavior

- 実行スクリプト: `scripts/policies/validate-cedar.mjs`
- 成果物: `artifacts/policies/cedar-summary.json`
- PR comment header: `<!-- AE-CEDAR-SUMMARY -->`
- Trigger: add label `run-security` (or `run-cedar`)
- Enforcement: add label `enforce-security` (fails when `ngCount > 0`)

### Environment variables

- `CEDAR_POLICIES_DIR`: directory to scan (default: `policies/cedar`)
- `CEDAR_SUMMARY`: output JSON path (default: `artifacts/policies/cedar-summary.json`)

### Minimal JSON structure

```json
{
  "tool": "cedar-validator",
  "dir": "policies/cedar",
  "filesScanned": 3,
  "jsonFiles": 2,
  "cedarFiles": 1,
  "okCount": 3,
  "ngCount": 0,
  "errors": [{ "file": "...", "kind": "json-parse", "message": "..." }],
  "results": [
    { "file": "...", "type": "json|cedar", "valid": true },
    { "file": "...", "type": "json|cedar", "valid": false }
  ],
  "timestamp": "..."
}
```

### Notes

- JSON validation is intentionally minimal. The checker looks for `policySet` or a `policies` array-like structure.
- Text `.cedar` files are only checked for non-empty content.
- The lane is report-only by default. Add `enforce-security` only when you want `ngCount > 0` to block the job.

## 日本語

この workflow は `policies/cedar/` 以下の `.json`（Cedar JSON）と `.cedar` / `.ced` ファイルを走査し、非ブロッキングの summary を生成します。

### 現在の挙動

- 実行スクリプト: `scripts/policies/validate-cedar.mjs`
- 成果物: `artifacts/policies/cedar-summary.json`
- PR comment header: `<!-- AE-CEDAR-SUMMARY -->`
- 起動条件: `run-security` または `run-cedar` ラベルを付与
- 強制条件: `enforce-security` ラベルを付与すると `ngCount > 0` で失敗させます

### 環境変数

- `CEDAR_POLICIES_DIR`: 走査対象ディレクトリ。既定値は `policies/cedar`
- `CEDAR_SUMMARY`: 出力 JSON パス。既定値は `artifacts/policies/cedar-summary.json`

### 最小 JSON 形状

```json
{
  "tool": "cedar-validator",
  "dir": "policies/cedar",
  "filesScanned": 3,
  "jsonFiles": 2,
  "cedarFiles": 1,
  "okCount": 3,
  "ngCount": 0,
  "errors": [{ "file": "...", "kind": "json-parse", "message": "..." }],
  "results": [
    { "file": "...", "type": "json|cedar", "valid": true },
    { "file": "...", "type": "json|cedar", "valid": false }
  ],
  "timestamp": "..."
}
```

### 注意事項

- JSON 検証は意図的に最小限です。チェッカーは `policySet` または `policies` の array-like structure の有無を確認します。
- テキスト `.cedar` ファイルは non-empty かどうかだけを確認します。
- このレーンは既定で報告専用（report-only）です。`ngCount > 0` を失敗条件にしたい PR のみ `enforce-security` を付けてください。
