# Spec-driven CI Roadmap (Draft)

## 目的
- Issue #1011 ステップ2〜4で必要となる CI ジョブ（generate-artifacts / model-based-tests / conformance）を段階的に実装するための骨子をまとめる。
- Issue #1012 Phase C の"省略項目の棚卸し"で参照できる作業項目リストを提供する。

## 構成案

### 1. generate-artifacts ジョブ
- プロトタイプ: `pnpm run generate:artifacts:preview` と `.github/workflows/generate-artifacts-preview.yml` で quickstart を実行し、`hermetic-reports/spec/generate-artifacts-diff.json` に差分サマリを出力。
  - サンプル: 差分が無い場合は `{ "targets": [{ "path": ..., "hasChanges": false }] }` のような JSON が出力され、差分がある場合は `files` に `NAME	path` が列挙される。
  - 直近のサマリ例:

    ```json
    {
      "generatedAt": "2025-10-04T06:21:09.137Z",
      "targets": [
        { "path": "tests/api/generated", "hasChanges": false },
        { "path": "artifacts/codex", "hasChanges": false },
        { "path": "artifacts/spec", "hasChanges": false }
      ]
    }
    ```
- 入力: `specs/formal/**`, `templates/**`, `ae-framework.yml`
- 出力: `tests/api/generated/**`, `artifacts/formal/**`, `artifacts/spec/**`
- 残課題
  - [ ] 生成物の整合性チェック（`git diff --exit-code` ではなく JSON/YAML 正規化）
  - [ ] CI 上での大量出力対策（`artifacts/spec` のフィルタリング）
  - [ ] `scripts/adapters/aggregate-artifacts.mjs` の再確認（依存コマンド現状未整備）

- ✅ ミニマムゲートとして `.github/workflows/spec-generate-model.yml` を追加し、`pnpm run generate:artifacts:preview` のドリフト検知と KvOnce property suite を fail fast で実行できるようにした。

### 2. model-based-tests ジョブ
- 目的: 仕様から生成された BDD / property / contract テストを最小構成で実行
- 候補ステップ
  - [ ] `pnpm vitest run --project property`（fast-check 系）
  - [ ] `pnpm run test:contracts --focus=kv-once` のような部分実行
  - [ ] 生成 BDD `.feature` ファイルのスモーク（Step lint 済み）
- 残課題: 生成ファイルの対象絞り込み、モックデータ提供方法

### 3. conformance ジョブ
- プロトタイプ: `scripts/trace/projector-kvonce.mjs` と `scripts/trace/validate-kvonce.mjs` を追加（NDJSON ログ→集計→簡易検証）。今後 Projector/Validator を本実装する際の土台とする。
  - サンプル: `samples/trace/kvonce-sample.ndjson` → projector → `kvonce-projection.json` → validator → `kvonce-validation.json` で pipeline を再現可能。
- 目的: 実装ログを Projector/Validator に通し、仕様と照合。
- 現状: 実サービスのログ取り込みを自動化する仕組みが未整備。CI ではサンプル/モック/外部 payload を選択可能。
- `.github/workflows/spec-generate-model.yml` に `trace-conformance` ジョブを追加し、Step Summary と PR コメントで `kvonce-validation.json` の結果を共有。
- Stage1: `kvonce_otlp_artifact` / `kvonce_otlp_payload_url` 入力と `scripts/trace/fetch-otlp-payload.mjs` により、外部 payload をダウンロードして検証パイプラインへ接続可能。
- TODO
  - [x] トレーススキーマ案（NDJSON）を `docs/trace/kvonce-trace-schema.md` として整理し、Issue #1011 にリンク
  - [x] Projector / Validator を整備し、`scripts/trace/run-kvonce-conformance.sh` で利用
  - [x] OTLP → NDJSON 変換（`scripts/trace/mock-otlp-service.mjs`, `scripts/trace/prepare-otlp-trace.mjs`, `scripts/trace/convert-otlp-kvonce.mjs`）を CI に統合
  - [ ] 実サービスの OTLP エクスポータからログを自動収集し、CI に取り込む設計をまとめる（`docs/trace/otlp-collector-plan.md` の TODO に展開／Stage2以降で実施）

### 4. Report / Dashboard
- 最終ステップで `spec-check` / `generate-artifacts` / `model-based-tests` / `conformance` の結果を集約
- 短期: GitHub Step Summary で JSON コンパクト表示
- 長期: ダッシュボード（Issue #1011 ステップ5）に引き継ぐ

## 次アクション候補
4. generate-artifacts-preview の PR トリガーは Step Summary にサマリを出すだけなので、将来的に PR コメントへ自動投稿するジョブ (comment drift) を導入予定。
1. Q4 中に generate-artifacts ジョブを設計するための spike ブランチを切り、差分検出方法を評価。
2. モデルベーステスト対象を `kv-once` のみで実行できるよう `tests/property/reservation-schema.property.test.ts` を分割・軽量化。
3. トレーススキーマのドラフトを `docs/TLA+/kv-once-poc.md` から派生させ、Issue #1011 に共有。
5. 自動生成された BDD/contract テストを対象に追加し、`model-based-tests` ジョブの網羅範囲を段階的に拡張。
