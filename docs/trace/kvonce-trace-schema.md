# KvOnce Trace Schema (Draft)

## 目的
- Issue #1011 ステップ3の準備として、KvOnce PoC 向けトレース形式を整理する。
- NDJSON ログを Projector (`scripts/trace/projector-kvonce.mjs`) に投入し、Validator (`scripts/trace/validate-kvonce.mjs`) で安全性を確認する際の入力仕様を定義する。

## イベントフォーマット
| フィールド | 型 | 必須 | 説明 |
|------------|----|------|------|
| `timestamp` | string (ISO8601) | ✓ | 実際のイベントが発生した UTC 時刻 |
| `type` | string (`success` \| `retry` \| `failure`) | ✓ | イベント種別 |
| `key` | string | ✓ | KvOnce キー |
| `value` | string | success時のみ | 書き込まれた値 |
| `reason` | string | failure時のみ | 失敗理由 |
| `context` | object | 任意 (retry時は `attempts` 必須) | 追加メタデータ。`type="retry"` の場合は `{ attempts: <number>, ... }` を含める |

## サンプル (NDJSON)
- `samples/trace/kvonce-sample.ndjson`（リポジトリに同梱。`--format ndjson` で即座に投入可能）

```ndjson
{"timestamp":"2025-10-04T06:00:00.000Z","type":"success","key":"alpha","value":"v1"}
{"timestamp":"2025-10-04T06:00:02.000Z","type":"failure","key":"beta","reason":"duplicate"}
{"timestamp":"2025-10-04T06:00:03.000Z","type":"retry","key":"beta"}
{"timestamp":"2025-10-04T06:00:04.000Z","type":"success","key":"beta","value":"v2"}
```

## OTLP Mapping
- `scripts/trace/mock-otlp-service.mjs` — Fastify + OpenTelemetry SDK を利用して ResourceSpans を生成。
- `scripts/trace/prepare-otlp-trace.mjs` — `KVONCE_OTLP_PAYLOAD` で指定された外部ログを優先し、未指定時はサンプルまたはモックサービスで payload を準備。
- `scripts/trace/convert-otlp-kvonce.mjs` — OTLP JSON を NDJSON に変換。`startTimeUnixNano` を ISO8601 に変換し、安全な整数範囲外は例外扱い。
- `scripts/trace/run-kvonce-conformance.sh` — NDJSON/OTLP を入力に Projection → Validation を実施し、`hermetic-reports/trace/<mode>/kvonce-validation.json` を出力。`--input` / `--output-dir` / `--format` を指定して手元ログや外部 Collector 出力を検証できる。

## CI への組み込み
- `.github/workflows/spec-generate-model.yml` の `trace-conformance` ジョブが `prepare-otlp-trace.mjs` → `run-kvonce-conformance.sh` のパイプラインを実行し、Step Summary および PR コメントに結果を出力。
- 生成物 (`collected-kvonce-otlp.json`, `kvonce-events.ndjson`, `kvonce-projection.json`, `kvonce-validation.json`) は `kvonce-trace` アーティファクトとして保存。

## 今後の拡張
- `docs/trace/otlp-collector-plan.md` に従い、実サービス Collector からのログダウンロードとシークレット管理を整備。
- 複数ドメイン向けに共通テンプレートを定義し、Issue #1011 Step3 の横展開を準備する。
