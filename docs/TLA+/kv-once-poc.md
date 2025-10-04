# KvOnce TLA+ PoC メモ

## 目的
- 単一書き込み（Key-Value Once）ドメインで TLA+ の抽象 → 精緻化 → 実装仕様の三層構成を確認する。
- TLC / Apalache を用いた最小限のモデルチェック手順を整備し、Issue #1011 ステップ1および Issue #1012 Phase B の準備とする。
- 将来的な generate / conformance 連携に向けた前提（イベント列や再試行挙動）を明文化する。

## モジュール構成
| 階層 | ファイル | 概要 |
|------|----------|------|
| 抽象 | `specs/formal/10_abstract/KvOnce.tla` | 一度だけ書き込める Key-Value ストアの安全性（NoOverwrite）を定義 |
| 準抽象 | `specs/formal/20_refined/KvOnceRefinement.tla` | 再試行（Retry）回数を制限しつつ書き込み成功を表現 |
| 実装 | `specs/formal/30_impl/KvOnceImpl.tla` | イベントログを保持し、成功 / リトライ / 失敗（重複）を記録 |
| Mapping | `specs/formal/mappings/KvOnce.impl.json` | 各層の状態変数対応およびイベントトレース情報 |
| cfg | `specs/formal/configs/*.cfg` | TLC / Apalache で利用する初期状態・定数定義 |

## 実行方法
ローカルで TLC / Apalache を実行する場合:

```bash
# TLC
pnpm run spec:kv-once:tlc

# Apalache
pnpm run spec:kv-once:apalache
```
- `scripts/formal/verify-tla.mjs` が両エンジンをラップしており、`timeout` コマンドや `TLA_TOOLS_JAR` / `apalache-mc` の有無を自動判定します。
- 実行結果は `hermetic-reports/formal/tla-summary.json` に書き出されます。CI ではステップごとにコピーし、`kvonce-tlc-summary.json` / `kvonce-apalache-summary.json` として保存しています。
- ツールが未インストールの場合は `status: tool_not_available` として非致命的に終了します（Issue #1012 Phase B ではインストール手順整備が残課題）。

## イベントモデル
- `KvOnceImpl.tla` では `events` シーケンスが `success / retry / failure` の三種類（`reason` は `STRING ∪ {NULL}`）で構成されています。
- 失敗イベント（`duplicate`）は `store[k].written` なキーに対してのみ発火するようガード済みです。
- 今後トレース検証を導入する際は、このイベント列を OTLP/NDJSON にマッピングして Projector → Validator に渡す想定です。

## 既知の制約 / TODO
- Projector / Validator の試作として `scripts/trace/projector-kvonce.mjs` と `scripts/trace/validate-kvonce.mjs` を用意しました（NDJSON ログ → 集計 → 簡易検証）。本実装では Issue #1011 ステップ3で拡張予定。
- Apalache 検証は最大 60 秒タイムアウトに設定しており、大きな状態空間を扱うには cfg の調整が必要です。
- kv-once PoC と minimal pipeline の成果物（formal summary など）の突合はまだ行っていません。Issue #1011 ステップ2で generate/conformance 連携に着手予定です。
- Issue #1012 Phase C で、後続フェーズに回す具体的なタスク（生成アーティファクト差分、トレーサ、ダッシュボードなど）の棚卸しを行います。

## 参考
- `docs/TLA+/tla_plus_full_integration.md` — 全体ロードマップ
- `scripts/trace/projector-kvonce.mjs`, `scripts/trace/validate-kvonce.mjs` — NDJSON ログを射影・検証する雛形（例: `hermetic-reports/trace/kvonce-sample.ndjson`).
- `docs/notes/verify-lite-lint-plan.md` — verify-lite lint 改善計画
- `.github/workflows/minimal-pipeline.yml` — TLC/Apalache を含む最小パイプライン
- `docs/trace/kvonce-trace-schema.md` — NDJSON トレースのドラフトスキーマと拡張メモ
- `scripts/trace/run-kvonce-conformance.sh` — Projector / Validator をまとめて実行し、`hermetic-reports/trace/` に結果を出力
- `samples/trace/kvonce-otlp.json` — OTLP ResourceSpans から NDJSON へ変換するためのサンプル入力
