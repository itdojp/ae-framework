# Reason Codes（reasonCode）Registry

本リポジトリでは、失敗要因の安定した分類キーとして `reasonCode` を導入する。

- 目的: 週次集計（SLO/MTTR運用）やアラートで、`reason`（自由記述）に依存せず集計・分類できるようにする。
- SSOT（辞書）: `policy/reason-codes.yml`

## 1. 仕様

- フィールド名: `reasonCode`（camelCase）
- フォーマット: 小文字 + ドット区切り（例: `policy.required_labels_missing`）
- 非推奨: 動的値（件数/PR番号/URLなど）を埋め込むコード

## 2. 運用

- `reasonCode` は「機械可読の分類キー」、`reason` は「人間向け補足」として併用する。
- 新規コード追加時は `policy/reason-codes.yml` に追記し、対応する emit/集計のテストを更新する。
- 変更時は次の validator を実行し、emit 側マッピングとの整合を確認する。  
  `pnpm run reason-codes:validate`

## 3. 検証導線（CI）

- `verify-lite` (`.github/workflows/verify-lite.yml`) / `minimal-pipeline` (`.github/workflows/minimal-pipeline.yml`) は `pnpm run verify:lite` を実行する。
- `pnpm run verify:lite` の実体である `scripts/ci/run-verify-lite-local.sh` が validator を 1 回だけ実行し、`verify-lite-run-summary` の `steps.reasonCodeRegistryValidation` に結果を記録する。
- 単体確認が必要な場合は `pnpm run reason-codes:validate` を直接実行する。

## 4. 参照

- Automation report（共通フォーマット）: `docs/ci/automation-observability.md`
- 週次集計（Top理由）: `scripts/ci/automation-observability-weekly.mjs`
