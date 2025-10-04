# OTLP Collector Integration Plan (Draft)

Issue: #1011 / #1012

## 背景
- KvOnce の trace-conformance ジョブは現在 `prepare-otlp-trace.mjs` を通じてサンプルまたはモック生成した OTLP payload を利用している。
- 実サービスの OTLP Exporter から収集したログを CI に取り込むため、Collector 構成とシークレット管理・アーティファクト受け渡し設計が必要。

## 想定アーキテクチャ
1. **Agent / Application** — OTLP HTTP/GRPC exporter を用いて Collector へ送信。
2. **Collector** — フィルタリング後、KVONCE 専用 sink (S3/GCS/GitHub Artifacts 等) に保存。
3. **CI (trace-conformance job)** — `KVONCE_OTLP_PAYLOAD` に指定した payload をダウンロードし、`prepare-otlp-trace.mjs` で展開、検証を実施。

## TODO
- [ ] Collector 出力先の決定（S3/GCS/Artifacts）。
- [ ] 認証方式（GitHub OIDC / PAT / Pre-signed URL）。
- [ ] payload サイズ・フォーマット・保持期間の決定。
- [ ] `scripts/trace/fetch-otlp-payload.mjs` の設計（ダウンロードと検証）。
- [ ] プライバシー/PII マスキングポリシー策定。

## 次ステップ
1. PoC: Collector → GitHub Artifacts アップロード → trace-conformance job がダウンロードして検証。
2. RFC 作成: 実環境への導入手順、Secrets 管理、fail-safe 方針。
3. 実装ロードマップを Issue #1011 Step3 / Issue #1012 Phase C に反映。
