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
   - 追加の成果物を添付する場合は `REPORT_ENVELOPE_PAYLOAD_METADATA`（単一ファイル）や `REPORT_ENVELOPE_EXTRA_ARTIFACTS`（カンマ区切りのパス列）を指定すると自動的に `artifacts` 配列へ追記される。
   - Envelope が揃っている場合は `pnpm verify:conformance --from-envelope artifacts/report-envelope.json` でトレースサマリを再掲でき、CI なしの環境でも Step Summary を再利用できる。
2. Envelope の生成時に `GITHUB_RUN_ID` / `GITHUB_WORKFLOW` / `GITHUB_SHA` / `GITHUB_REF` を自動埋め込み、他の CI でも環境変数から補完できるようにする。
3. `REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE` を設定すると `tempoLinks[]` に Tempo Explore への URL が追加され、Step Summary やダッシュボードから対象 trace をすぐ開ける（例: `https://tempo.example.com/explore?traceId={traceId}`）。

### GitHub へのコメント展開
- `scripts/trace/post-envelope-comment.mjs` を使うと、Envelope の内容を GitHub Issue / Pull Request コメントとして展開できる。
  - `node scripts/trace/post-envelope-comment.mjs --envelope artifacts/trace/report-envelope.json --dry-run` で出力を確認。
  - 実際に投稿する場合は `--repo <owner/repo>` と `--issue`（または `--pr`）を指定し、`gh` CLI が利用可能な環境で実行する。
  - コメントには Trace IDs、Tempo Links、Artifacts、Cases などが Markdown で整形され、Slack や GitHub 上での共有を容易にする。
4. Trace 系ジョブでは、Collector から取得した payload のメタデータ (`kvonce-payload-metadata.json`) を artifacts 配列に追加し、`scripts/trace/build-kvonce-envelope-summary.mjs` で集計したサマリを `scripts/trace/create-report-envelope.mjs` でラップする。
5. Dashboard / Tempo 連携は Envelope を単位としてインジェストし、必要に応じて `traceIds` から関連 span を引き直す。
6. S3 などに Envelope を保存する場合は `scripts/trace/upload-envelope.mjs`（AWS CLI 要）を利用し、`REPORT_ENVELOPE_OUTPUT` を指すファイルを `REPORT_ENVELOPE_S3_BUCKET` / `REPORT_ENVELOPE_S3_KEY` でアップロードする。
7. presigned URL や Slack 通知が必要な場合は `scripts/trace/publish-envelope.mjs` を利用する。`--dry-run` でプレビュー後、`--bucket` 等を指定して `upload-envelope` → `aws s3 presign` → Slack 通知までを一括で実行できる。

## OTLP Attribute Mapping
| Envelope Field | OTLP Span Attribute | 説明 |
|---------------|---------------------|------|
| `correlation.traceIds[]` | `trace_id` | Envelope と Tempo trace を突き合わせるための ID。`pipelines:trace` が Projector/Validator 実行時に書き戻す。 |
| `correlation.runId` | `kvonce.run_id` | GitHub Actions の `GITHUB_RUN_ID`。Tempo では `kvonce.run_id` で TraceQL フィルタを行う。 |
| `summary.validation.valid` | `kvonce.validation.valid` | Validator の結果を Tempo 側でも可視化するための boolean 属性。 |
| `summary.projection.events` | `kvonce.projection.event_count` | Projector によるイベント件数。多すぎる／少なすぎるケースを Tempo で検知できる。 |
| `artifacts[].path` | `kvonce.artifact_path` | Projection/Validation/TLC の成果物パス。Grafana Link パネルから直接ダウンロードできるようにする。 |
| `metadata.branch` (予定) | `kvonce.branch` | CI ブランチ名。Tempo の TraceQL で `kvonce.branch = 'main'` のように範囲指定する。 |

> ℹ️ **属性の付与ポイント**: `scripts/trace/build-kvonce-envelope-summary.mjs` で Envelope を組み立てた後、Collector や Tempo に投入する際に同じ値を span attributes (`kvonce.*`) としてコピーする。Collector 再取得時もこの表を参照し、欠損していれば `pipelines:trace` で警告を表示する。

## Step Summary レイアウト指針
Verify Lite / Trace / Spec ジョブの Step Summary は以下の順で統一する。
1. **Spec**: TLC / Apalache の結果 (`spec:kv-once:*`)。成功可否と探索境界のメモを 1 行で表示。
2. **Verify Lite**: lint / mutation quick / property test の集計。Envelope の `summary.steps.*` を短く要約し、差分があれば notes に残す。
3. **Trace**: `verify:conformance` が出力する Projection/Validation/TLC 成果。`summary.trace` から status / issues 数を抜粋する。

`verify-conformance.mjs` は上記フォーマットで Step Summary を出力するよう更新済み。今後 `pipelines:full` や `pipelines:trace` でも同一フォーマットを利用するため、共通テンプレートを `scripts/ci/step-summary.ts`（次フェーズで作成予定）に切り出す。

## TODO / 状態
- [x] JSON Schema を `schema/report-envelope.schema.json` として整備し、AJV で検証する。（PR #1043）
- [x] Verify Lite ワークフローで Envelope 生成＋ Artifact アップロードまで自動化する（PR #1044, #1048）。
- [x] Trace conformance ジョブで Projector/Validator の出力を Envelope にまとめ、Issue #1011 Step3 の完了条件に組み込む（PR #1049）。
- [ ] 将来的に `artifacts` へ S3 Presigned URL を許容する場合の署名方式を整理する。
