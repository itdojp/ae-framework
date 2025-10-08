# Trace Step3 Readiness (2025-10-09)

## 完了済みの前提条件
- Report Envelope schema / AJV 検証（PR #1043, #1044）
- Stage2 fetch & payload metadata (PR #1045〜#1049)
- MinIO PoC & AWS OIDC ノート（PR #1050 / docs/trace/aws-oidc-integration.md）
- KvOnce トレースパスの Envelope 統合（PR #1049）
- `pnpm pipelines:full` で Verify Lite → Pact → API fuzz → mutation quick を通すプロトタイプ

## 現状の Blocker 状況
- Verify Lite lint backlog: `pipelines:full` の `--skip` オプションで段階導入可能 → Blocker 解除済み
- mutation quick レポート: `pipelines:mutation:*` コマンドで 10〜12 分の quick run を再現可能（最新スコア 72.02%）
- collector Stage2: MinIO / S3 経路を docs に整理済み。OIDC 経由は #1015 連動で実装予定。

## Step3 作業キュー（Issue #1011 へ転記予定）
1. Projector v1
   - NDJSON → spec state 射影。
   - スキーマ: `docs/trace/kvonce-trace-schema.md`
   - 出力: `hermetic-reports/trace/kvonce-projection.json` / `hermetic-reports/trace/projected/kvonce-state-sequence.json`
2. Validator v1
   - Projector 出力を TLC/Apalache に投入し、不変条件と遷移差分を比較。
   - CLI: `pnpm verify:conformance --from-envelope`
3. CI 統合
   - GitHub Actions: `verify-trace` job を `pipelines:full` の後段に追加（opt-in ラベル運用）。
   - 成果物: report envelope + projected trace + TLC result を artifact 化。
4. Dashboards 準備
   - Tempo/Grafana ノートを Issue #1015 から移植。
   - Envelope の `metadata` → Tempo span attributes のマッピング表を docs に追記。

## 推奨される次手順
- `pnpm pipelines:trace --input samples/trace/kvonce-sample.ndjson` で projector → validator → TLC の最小フローを一括実行し、`hermetic-reports/trace/` 以下にレポートを生成する。
- Issue #1011 を編集し、本ドキュメントの Step3 作業キューをチェックリスト化する。
- Stage3 実装タスクを小さな PR 単位（Projector, Validator, CI, Dashboard）に分割。
- Verify Lite ワークフローに `pipelines:full` の mutation quick 結果を Step Summary として添付。
