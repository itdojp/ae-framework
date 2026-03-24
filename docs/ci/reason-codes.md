---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Reason Codes（reasonCode）Registry

Primary sources / 一次情報:
- `policy/reason-codes.yml`
- `scripts/ci/run-verify-lite-local.sh`

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document defines the stable `reasonCode` classification keys used by automation and CI reports.

The repository uses `reasonCode` as a stable machine-readable classification key for failures and skips.

Primary goal:
- weekly aggregation, SLO/MTTR analysis, and alerting can classify incidents without depending on free-text `reason`

SSOT dictionary:
- `policy/reason-codes.yml`

### 2. Contract

- Field name: `reasonCode` (camelCase)
- Format: lowercase + dot-separated segments
  - example: `policy.required_labels_missing`
- Anti-pattern:
  - do not embed dynamic values such as counts, PR numbers, SHAs, or URLs into the code itself

Operational split:
- `reasonCode`: stable machine-readable category
- `reason`: human-readable supplemental detail

### 3. Operating rules

- add new codes only through `policy/reason-codes.yml`
- when a new code is added, update both emit-side tests and aggregation-side tests
- keep emitters and validators aligned so that weekly observability and downstream alerts can aggregate by stable keys

The contract is intentionally conservative: emitters may change `reason`, but they should not drift the `reasonCode` taxonomy casually because that breaks trend continuity.

### 4. Validation path in CI

- `verify-lite` (`.github/workflows/verify-lite.yml`) and `minimal-pipeline` (`.github/workflows/minimal-pipeline.yml`) run `pnpm run verify:lite`
- `scripts/ci/run-verify-lite-local.sh` executes the validator exactly once and records the result into the artifact `artifacts/verify-lite/verify-lite-run-summary.json` at JSON path `/steps/reasonCodeRegistryValidation`
- for focused local verification, run `pnpm run reason-codes:validate` directly

Minimum regression command:

```bash
pnpm run reason-codes:validate
```

### 5. References

- shared automation report contract: `docs/ci/automation-observability.md`
- weekly failure aggregation: `scripts/ci/automation-observability-weekly.mjs`

## 日本語

本ドキュメントは、自動化および CI レポートで使用する安定した分類キー `reasonCode` を定義します。

本リポジトリでは、失敗要因の安定した分類キーとして `reasonCode` を導入する。

- 目的: 週次集計（SLO/MTTR運用）やアラートで、`reason`（自由記述）に依存せず集計・分類できるようにする。
- SSOT（辞書）: `policy/reason-codes.yml`

### 1. 仕様

- フィールド名: `reasonCode`（camelCase）
- フォーマット: 小文字 + ドット区切り（例: `policy.required_labels_missing`）
- 非推奨: 動的値（件数/PR番号/URLなど）を埋め込むコード

補足:
- `reasonCode` は安定した機械可読キー
- `reason` は人間向け補足

### 2. 運用

- `reasonCode` は「機械可読の分類キー」、`reason` は「人間向け補足」として併用する。
- 新規コード追加時は `policy/reason-codes.yml` に追記し、対応する emit/集計のテストを更新する。
- 安定した trend を壊さないため、`reason` を変更しても `reasonCode` の taxonomy は不用意に変更しない。
- 変更時は次の validator を実行し、emit 側マッピングとの整合を確認する。  
  `pnpm run reason-codes:validate`

### 3. 検証導線（CI）

- `verify-lite` (`.github/workflows/verify-lite.yml`) / `minimal-pipeline` (`.github/workflows/minimal-pipeline.yml`) は `pnpm run verify:lite` を実行する。
- `pnpm run verify:lite` の実体である `scripts/ci/run-verify-lite-local.sh` が validator を 1 回だけ実行し、成果物 `artifacts/verify-lite/verify-lite-run-summary.json` の JSON path `/steps/reasonCodeRegistryValidation` に結果を記録する。
- 単体確認が必要な場合は `pnpm run reason-codes:validate` を直接実行する。

### 4. 参照

- Automation report（共通フォーマット）: `docs/ci/automation-observability.md`
- 週次集計（Top理由）: `scripts/ci/automation-observability-weekly.mjs`
