# KvOnce Trace Schema

## 目的
- Issue #1011 ステップ3の準備として、KvOnce PoC 向けの最小トレース形式を整理します。
- NDJSON ログを Projector (`scripts/trace/projector-kvonce.mjs`) に投入し、Validator (`scripts/trace/validate-kvonce.mjs`) で安全性を確認する際の入力仕様を定義します。

## 共通必須項目（Issue #2391）
| フィールド | 型 | 契約上の扱い | 説明 |
|------------|----|--------------|------|
| `traceId` | string | 必須（report-only） | Run/Span 相関に使う識別子。NDJSON ではトップレベル、OTLP では `span.traceId` を基準とする。 |
| `timestamp` | string (ISO8601) | 必須（report-only） | イベント発生時刻（UTC）。`projector-kvonce` は値を保持し、並び順は入力順に依存する。 |
| `actor` | string | 必須（report-only） | イベント発生主体（例: `kvonce-client`、`kvonce-worker`）。 |
| `event` | string (`success` \| `retry` \| `failure`) | 必須（report-only） | 正規化したイベント種別。 |

> 運用注記（Issue #2391）: 上記4項目は report-only 契約です。  
> `run-kvonce-conformance.sh` / `validate-kvonce.mjs` では Required 化せず、欠落時も失敗条件にはしません。

## NDJSON イベントフォーマット
| フィールド | 型 | 必須 | 説明 |
|------------|----|------|------|
| `traceId` | string | 契約必須（report-only） | 共通必須項目。イベント間相関に利用。 |
| `timestamp` | string (ISO8601) | ✓ | 仕様イベントが発生したUTC時刻。`projector-kvonce` はこの値を保持し、並び順は入力順に依存する。 |
| `actor` | string | 契約必須（report-only） | 共通必須項目。イベント発生主体。 |
| `event` | string (`success` \| `retry` \| `failure`) | 契約必須（report-only） | 共通必須項目。 |
| `type` | string (`success` \| `retry` \| `failure`) | ✓ | 現行実装の互換入力キー。`event` と同値を設定して運用する。 |
| `key` | string | ✓ | KvOnce キー。仕様上は有限集合 `Keys` の値。 |
| `value` | string | success時のみ | 書き込まれた値。必要に応じてハッシュなどに置き換え。 |
| `reason` | string | failure時のみ | 失敗理由（例: `duplicate`, `timeout`）。 |
| `context` | object \| string \| number | 任意 | 追加メタデータ（HTTP ステータスやトレースIDなど）。`retry` の場合は `attempt`/`attempts` (number) を含めると検証が強化される。 |

## サンプル
- `samples/trace/kvonce-sample.ndjson`

```ndjson
{"traceId":"kvonce-trace-001","timestamp":"2025-10-04T06:00:00.000Z","actor":"kvonce-client","event":"success","type":"success","key":"alpha","value":"v1"}
{"traceId":"kvonce-trace-001","timestamp":"2025-10-04T06:00:02.000Z","actor":"kvonce-client","event":"failure","type":"failure","key":"beta","reason":"duplicate"}
{"traceId":"kvonce-trace-001","timestamp":"2025-10-04T06:00:03.000Z","actor":"kvonce-worker","event":"retry","type":"retry","key":"beta"}
{"traceId":"kvonce-trace-001","timestamp":"2025-10-04T06:00:04.000Z","actor":"kvonce-client","event":"success","type":"success","key":"beta","value":"v2"}
```

## Projector / Validator
- `scripts/trace/projector-kvonce.mjs`
  - NDJSON を読み込み、キー単位の成功回数・再試行回数・失敗理由一覧、直近の `value` を集計します。
  - `stats` にイベント種別の件数・ユニークキー数・成功率などを格納し、Envelope から簡易チェックが可能です。
  - `--state-output artifacts/hermetic-reports/trace/projected/kvonce-state-sequence.json` を指定すると、イベントごとの射影状態（`store[key]` の `written` / `value` / `retries` など）を別ファイルとして書き出します。
  - `retryContexts` / `successContexts` / `failureContexts` として、元イベントの `context` を配列で保持します。
- `scripts/trace/validate-kvonce.mjs`
  - KvOnce の安全性（1回書き込み・再試行上限）を確認し、`kvonce-validation.json` に集計結果を出力します。
  - `retryContexts` に `attempt` または `attempts` を含めると、連番チェックと成功の整合性チェックが有効化されます。
- `scripts/trace/run-kvonce-conformance.sh`
  - 上記の両スクリプトを連続起動し、結果を `artifacts/hermetic-reports/trace/` に保存します。CI では `spec-generate-model` ワークフロー内で利用。
- `scripts/trace/run-kvonce-trace-replay.mjs`
  - KvOnce サンプルトレースを検証したうえで、TLC (`pnpm run spec:kv-once:tlc`) を実行し、`artifacts/hermetic-reports/trace/replay/kvonce-trace-replay.json` にサマリを出力します。
  - TLC ツールが未導入の場合は `tool_not_available` として記録しつつ、CI ではステップサマリに結果を追記します。
- `scripts/trace/build-kvonce-envelope-summary.mjs`
  - `--trace-dir` / `--summary` オプションを指定することで `artifacts/kvonce-trace-summary.json` に最新 Run の統計・成果物パス・`verify:conformance` のサマリを集約できます。

## 今後の拡張
- Issue #1011 ステップ3: 生成されたトレースを実装ログから自動抽出し、このスキーマに準拠させる。
- Issue #1011 ステップ4: `verify:conformance` ワークフローに統合し、CIゲートとして運用。
- Issue #1012 Phase C: 他ドメイン仕様のトレーススキーマも同様の形式で整理する。

## OTLP Mapping
- OTLP span属性からの対応:
  - `span.traceId` → `traceId`
  - `span.startTimeUnixNano` → `timestamp`（ISO8601）
  - `kvonce.actor` → `actor`
  - `kvonce.event.type` → `event`（現行変換では互換キー `type` として出力）
  - `kvonce.event.key` → キー
  - `kvonce.event.value` → 成功時の値
  - `kvonce.event.reason` → 失敗理由
  - `kvonce.event.context` → 任意メタデータ。mapValue は JSON オブジェクトとして埋め込まれる
- 現行 `scripts/trace/convert-otlp-kvonce.mjs` は `kvonce.event.type` と `kvonce.event.key` を必須判定に使い、出力イベントには互換キー `type` を使用します。`traceId` / `actor` / `event` は report-only 契約として扱います。
- `scripts/trace/convert-otlp-kvonce.mjs` が OTLP JSON を NDJSON 形式に変換します。デフォルトでは span の `startTimeUnixNano` を ISO8601 に変換し、必要な属性が欠けているイベントはスキップします。
- フォールバックとして `samples/trace/kvonce-otlp.json` / `samples/trace/kvonce-sample.ndjson` を提供し、CI が外部コレクタがなくても検証できるようにしています。
- CI では `scripts/trace/run-kvonce-conformance.sh --format otlp --input samples/trace/kvonce-otlp.json` を利用して、自動的に変換→検証を行います。
