# KvOnce Trace Schema (Draft)

## 目的
- Issue #1011 ステップ3の準備として、KvOnce PoC 向けの最小トレース形式を整理します。
- NDJSON ログを Projector (`scripts/trace/projector-kvonce.mjs`) に投入し、Validator (`scripts/trace/validate-kvonce.mjs`) で安全性を確認する際の入力仕様を定義します。

## イベントフォーマット
| フィールド | 型 | 必須 | 説明 |
|------------|----|------|------|
| `timestamp` | string (ISO8601) | ✓ | 仕様イベントが発生したUTC時刻。 |
| `type` | string (`success` \| `retry` \| `failure`) | ✓ | イベント種別。`success` は書き込み成功、`retry` は再試行、`failure` は失敗を表す。 |
| `key` | string | ✓ | KvOnce キー。仕様上は有限集合 `Keys` の値。 |
| `value` | string | success時のみ | 書き込まれた値。必要に応じてハッシュなどに置き換え。 |
| `reason` | string | failure時のみ | 失敗理由（例: `duplicate`, `timeout`）。 |
| `context` | object | 任意 | 追加メタデータ（HTTP ステータスやトレースIDなど）。 |

## サンプル
- `samples/trace/kvonce-sample.ndjson`

```ndjson
{"timestamp":"2025-10-04T06:00:00.000Z","type":"success","key":"alpha","value":"v1"}
{"timestamp":"2025-10-04T06:00:02.000Z","type":"failure","key":"beta","reason":"duplicate"}
{"timestamp":"2025-10-04T06:00:03.000Z","type":"retry","key":"beta"}
{"timestamp":"2025-10-04T06:00:04.000Z","type":"success","key":"beta","value":"v2"}
```

## Projector / Validator
- `scripts/trace/projector-kvonce.mjs`
  - NDJSON を読み込み、キー単位の成功回数・再試行回数・失敗理由一覧を集計します。
- `scripts/trace/validate-kvonce.mjs`
  - KvOnce の安全性（1回書き込み・再試行上限）を確認し、`kvonce-validation.json` に集計結果を出力します。
- `scripts/trace/run-kvonce-conformance.sh`
  - 上記の両スクリプトを連続起動し、結果を `hermetic-reports/trace/` に保存します。CI では `spec-generate-model` ワークフロー内で利用。

## 今後の拡張
- Issue #1011 ステップ3: 生成されたトレースを実装ログから自動抽出し、このスキーマに準拠させる。
- Issue #1011 ステップ4: `verify:conformance` ワークフローに統合し、CIゲートとして運用。
- Issue #1012 Phase C: 他ドメイン仕様のトレーススキーマも同様の形式で整理する。
