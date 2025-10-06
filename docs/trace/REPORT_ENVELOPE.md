# Report Envelope Specification (Draft)

Issue: #1011 / #1012 / #1036 / #1038

## 背景
- Verify Lite や trace-conformance など複数のジョブが、個別形式のサマリ JSON を生成している。
- 今後、Projector / Validator / Dashboard で横断的に扱うために、最小限の **共通コンテナ (Envelope)** を定義し、CI でも生成・受け渡し可能にする。
- Envelope は、元データをそのまま埋め込むのではなく、**メタデータ + 参照情報 (Artifacts)** を構造化して記録する。

## ゴール
1. Verify Lite run summary など既存成果物のラップ形式を定義する。
2. Trace PoC (KvOnce) から生成される集計結果と相関フィールドを整備する。
3. 将来的に Collector / Tempo / Dashboard へ連結する際の中間表現として利用する。

## フォーマット概要
| フィールド | 型 | 必須 | 説明 |
|------------|----|------|------|
| `schemaVersion` | string (semver) | ✓ | Envelope 自身のバージョン。破壊的変更時は major++。初期値は `1.0.0`。 |
| `source` | string | ✓ | 発生元となるパイプライン ID (例: `verify-lite`, `trace-conformance` 等)。 |
| `generatedAt` | string (ISO8601) | ✓ | Envelope を生成した UTC 時刻。 |
| `correlation` | object | ✓ | CI 実行やトレースとの相関を表すフィールド群。 |
| `correlation.runId` | string | ✓ | CI 実行 ID (GitHub Actions の場合 `GITHUB_RUN_ID`)。
| `correlation.workflow` | string | ✓ | ワークフロー名または job 名。 |
| `correlation.commit` | string | ✓ | 対象コミット SHA。 |
| `correlation.branch` | string | ✓ | 対象ブランチ (短縮表記)。 |
| `correlation.traceIds` | string[] | - | OTLP Span や replay 実行など、関連する trace/span ID のリスト。 |
| `summary` | object | ✓ | 元サマリ JSON の抜粋 (Verify Lite の場合は `verify-lite-run-summary.json`)。大きすぎる場合は要約を入れ、完全版は artifacts で参照。 |
| `artifacts` | array | ✓ | 付随成果物のリスト。各要素は `type` / `path` / `checksum` / `description` を持つ。 |
| `notes` | array (string) | - | 補足メッセージ。CI で WARNING を並べる用途。 |

## JSON スキーマ (抜粋)
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "AE Framework Report Envelope",
  "type": "object",
  "required": ["schemaVersion", "source", "generatedAt", "correlation", "summary", "artifacts"],
  "properties": {
    "schemaVersion": { "type": "string", "pattern": "^\\d+\\.\\d+\\.\\d+$" },
    "source": { "type": "string", "minLength": 1 },
    "generatedAt": { "type": "string", "format": "date-time" },
    "correlation": {
      "type": "object",
      "required": ["runId", "workflow", "commit", "branch"],
      "properties": {
        "runId": { "type": "string", "minLength": 1 },
        "workflow": { "type": "string", "minLength": 1 },
        "commit": { "type": "string", "minLength": 1 },
        "branch": { "type": "string", "minLength": 1 },
        "traceIds": {
          "type": "array",
          "items": { "type": "string", "minLength": 1 }
        }
      },
      "additionalProperties": false
    },
    "summary": { "type": "object" },
    "artifacts": {
      "type": "array",
      "minItems": 1,
      "items": {
        "type": "object",
        "required": ["type", "path"],
        "properties": {
          "type": { "type": "string", "minLength": 1 },
          "path": { "type": "string", "minLength": 1 },
          "checksum": { "type": ["string", "null"], "pattern": "^sha256:[0-9a-f]{64}$" },
          "description": { "type": ["string", "null"], "minLength": 1 }
        },
        "additionalProperties": false
      }
    },
    "notes": {
      "type": "array",
      "items": { "type": "string", "minLength": 1 }
    }
  },
  "additionalProperties": false
}
```

## サンプル
```json
{
  "schemaVersion": "1.0.0",
  "source": "verify-lite",
  "generatedAt": "2025-10-06T02:30:00.000Z",
  "correlation": {
    "runId": "18268371063",
    "workflow": "Verify Lite",
    "commit": "01a5c13d",
    "branch": "refs/heads/main",
    "traceIds": ["9b9fe1f2ce9f6f47"]
  },
  "summary": {
    "schemaVersion": "1.0.0",
    "timestamp": "2025-10-06T02:29:59.000Z",
    "flags": {
      "install": "--frozen-lockfile",
      "noFrozen": false,
      "keepLintLog": true,
      "enforceLint": true,
      "runMutation": true
    },
    "steps": {
      "install": { "status": "success" },
      "lint": { "status": "failure", "notes": "baseline +5" },
      "mutationQuick": { "status": "success", "notes": "score: 65.51%" }
    }
  },
  "artifacts": [
    {
      "type": "application/json",
      "path": "artifacts/verify-lite/verify-lite-run-summary.json",
      "checksum": "sha256:3a8174c00a73b60bb8f5b7b3a0b989ca7cc5e4d2e29ac2b36a4d4c1a7cb29b90",
      "description": "Raw verify-lite run summary"
    }
  ],
  "notes": [
    "lint baseline enforced: +12 over threshold",
    "mutation survivors reported separately"
  ]
}
```

## バージョニング方針
- Envelope 自身の互換性を `schemaVersion` で管理する。構造に破壊的変更がある場合は major を更新。
- 埋め込む `summary` はソース固有の schemaVersion を保持し、Envelope 側は透過的に扱う。
- `artifacts.checksum` は `sha256:<hex>` 形式を推奨。未取得の場合は `null` を許容する。

## 運用ガイドライン
1. CI では `scripts/trace/create-report-envelope.mjs` を利用し、Verify Lite などのサマリを Envelope 化して `artifacts/report-envelope.json` に保存する。
   - スキーマは `schema/report-envelope.schema.json` で管理し、`scripts/ci/validate-report-envelope.mjs` で検証する。
2. Envelope の生成時に `GITHUB_RUN_ID` / `GITHUB_WORKFLOW` / `GITHUB_SHA` / `GITHUB_REF` を自動埋め込み、他の CI でも環境変数から補完できるようにする。
3. Trace 系ジョブでは、Collector から取得した payload のメタデータ (`kvonce-payload-metadata.json`) を artifacts 配列に追加し、`scripts/trace/build-kvonce-envelope-summary.mjs` で集計したサマリを `scripts/trace/create-report-envelope.mjs` でラップする。
4. Dashboard / Tempo 連携は Envelope を単位としてインジェストし、必要に応じて `traceIds` から関連 span を引き直す。

## TODO
- [ ] JSON Schema を `schema/report-envelope.schema.json` として整備し、AJV で検証する。
- [ ] Verify Lite ワークフローで Envelope 生成＋ Artifact アップロードまで自動化する (#1036 Section3)。
- [ ] Trace conformance ジョブで Projector/Validator の出力を Envelope にまとめ、Issue #1011 Step3 の完了条件に組み込む。
- [ ] 将来的に `artifacts` へ S3 Presigned URL を許容する場合の署名方式を整理する。
