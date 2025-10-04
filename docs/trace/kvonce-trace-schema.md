# KvOnce Trace Schema (Draft)

## 目的
- Issue #1011 ステップ3の準備として、KvOnce PoC 向けのトレース形式を整理する。
- NDJSON ログを Projector (`scripts/trace/projector-kvonce.mjs`) に投入し、Validator (`scripts/trace/validate-kvonce.mjs`) で安全性を確認する際の入力仕様を定義する。

## イベントフォーマット
| フィールド | 型 | 必須 | 説明 |
|------------|----|------|------|
| `timestamp` | string (ISO8601) | ✓ | 仕様イベントが発生した UTC 時刻 |
| `type` | string (`success` \| `retry` \| `failure`) | ✓ | イベント種別 |
| `key` | string | ✓ | KvOnce キー |
| `value` | string | success時のみ | 書き込まれた値 |
| `reason` | string | failure時のみ | 失敗理由 |
| `context` | object | 任意 | 追加メタデータ |

## サンプル (NDJSON)
- `samples/trace/kvonce-sample.ndjson`

```ndjson
{"timestamp":"2025-10-04T06:00:00.000Z","type":"success","key":"alpha","value":"v1"}
{"timestamp":"2025-10-04T06:00:02.000Z","type":"failure","key":"beta","reason":"duplicate"}
{"timestamp":"2025-10-04T06:00:03.000Z","type":"retry","key":"beta"}
{"timestamp":"2025-10-04T06:00:04.000Z","type":"success","key":"beta","value":"v2"}
```

## OTLP Mapping
- OTLP span 属性との対応:
  - `kvonce.event.type` → イベント種別
  - `kvonce.event.key` → キー
  - `kvonce.event.value` → 成功時の値
  - `kvonce.event.reason` → 失敗理由
  - `kvonce.event.context` → 任意メタデータ
- `scripts/trace/mock-otlp-service.mjs` が Fastify ベースのモックサービスを起動し、OpenTelemetry SDK を利用して `hermetic-reports/trace/collected-kvonce-otlp.json` に ResourceSpans を出力します。
- `scripts/trace/prepare-otlp-trace.mjs` は `KVONCE_OTLP_PAYLOAD` 環境変数で指定された外部ログを優先的にコピーし、未指定の場合はサンプル/モックサービスを利用して同じ場所に payload を準備します。
- `scripts/trace/convert-otlp-kvonce.mjs` が OTLP JSON を NDJSON 形式に変換します。`startTimeUnixNano` は ISO8601 に変換し、安全な整数範囲外は例外扱いにします。
- `scripts/trace/run-kvonce-conformance.sh` は NDJSON/OTLP のいずれかを受け取り、Projection → Validation を実行して結果を `hermetic-reports/trace/kvonce-validation.json` に保存します。

## CI への組み込み
- `.github/workflows/spec-generate-model.yml` の `trace-conformance` ジョブが `prepare-otlp-trace` → `run-kvonce-conformance` のパイプラインを実行し、Step Summary に結果を出力します。
- 生成物 (`collected-kvonce-otlp.json`, `kvonce-projection.json`, `kvonce-validation.json`) は `kvonce-trace` アーティファクトとして保存されます。

## 今後の拡張
- Issue #1011 ステップ3: 実サービスの OTLP エクスポータからログを自動収集する仕組みを設計する。
- Issue #1011 ステップ4: `verify:conformance` ワークフローで OTLP 由来の検証結果をゲートに統合する。
- Issue #1012 Phase C: 他ドメイン仕様用のスキーマテンプレートを策定する。
