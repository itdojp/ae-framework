# CodeX CLI 0.38 × ae‑framework プレイブック実行ガイド

本書は、CodeX CLI 0.38 から ae‑framework のプレイブックを実行し、セットアップ→軽量QA→Spec/IR→Sim→Formal（任意）→Coverage/Adapters 検出→PRサマリ反映までを一気通貫で動かすための実践ガイドです。

## 前提（環境/権限）
- 実行場所
  - ローカル開発端末（推奨）: Node.js 18+、Git、pnpm、任意で gh（GitHub CLI）/CodeX CLI 0.38
  - CI（GitHub Actions）: PRコメントのスラッシュコマンド（例: `/verify-lite`）で検証を起動
- 権限
  - ローカル実行: 権限不要（リポジトリのクローンがあれば可）
  - ブランチ/PR作成・マージ: リポジトリへの Write 以上
  - 管理者マージ（要件未達でも取り込み）: Admin 権限
- Formalツール（任意）
  - Apalache/TLC は presence ガード済（未導入なら自動スキップ）。導入時のみ PATH/TLA_TOOLS_JAR 設定が必要

## 主要ファイル
- プレイブック本体: `scripts/codex/ae-playbook.mjs`
- プリセット（CodeX向け）: `codex/ae.playbook.yaml`
- npm補助スクリプト: `package.json`（`scripts.codex:run`）
- 設計/仕様ドキュメント: `docs/codex/ae-playbook.md`
- 本ガイド: `docs/codex/ae-playbook-usage.md`
- PRサマリ生成: `scripts/summary/render-pr-summary.mjs`

## 成果物（アーティファクト）
- コンテキスト: `artifacts/ae/context.json`
  - 各フェーズの結果・ログ・検出ファイルパス（coverage/adapters 等）を記録
- フェーズログ: `artifacts/ae/<phase>/*.log`
- Formal要約: `hermetic-reports/formal/{tla-summary.json, apalache-summary.json, apalache-output.txt}`
- Coverage検出: `coverage/coverage-summary.json`（優先）または `artifacts/coverage/coverage-summary.json`
- Adapters検出: `artifacts/adapters/**/summary.json`, `artifacts/lighthouse/summary.json` など
- Adapters検証: `artifacts/ae/adapters/adapters-validation.json`（{count, warnings[]}; 警告のみ）
- PRサマリ: `artifacts/summary/PR_SUMMARY.md`

## 実行シナリオ（ローカル）
1) 軽量ルート（Formalなし）
- 目的: セットアップ→軽量QA→Spec/IR→Sim→Coverage/Adapters 検出まで
- コマンド（いずれか）
  - `node scripts/codex/ae-playbook.mjs --resume --skip=formal`
  - `pnpm run codex:run`（= `--resume` のショートカット）

2) Formal を含む（オプトイン）
- 目的: 上記に Formal（Apalache/TLA）要約を追加収集
- コマンド: `node scripts/codex/ae-playbook.mjs --resume --enable-formal --formal-timeout=60000`
- 備考: GNU timeout があれば適用。ツール未導入時は `tool_not_available` でスキップ

3) 検出のみ（Coverage/Adapters の収集）
- 目的: 実行負荷を避けつつ検出情報だけ更新（report-only）
- コマンド: `node scripts/codex/ae-playbook.mjs --resume --skip=setup,qa,spec,sim,formal`

4) CodeX プリセット（任意）
- `codex/ae.playbook.yaml` にプリセットを用意
  - `playbook:light`: setup→qa→spec→sim（Formalなし）
  - `playbook:formal`: Formal込み（`--formal-timeout=60000`）
  - `playbook:detect`: Coverage/Adapters 検出のみ（report-only）

## フラグ/挙動
- `--resume`: 既存 `artifacts/ae/context.json` を読み、再開・更新
- `--skip=<csv>`: スキップ対象（例: `setup,qa,spec,sim,formal,coverage,adapters`）
- `--enable-formal`: Formalフェーズを実行（presenceガード/非ブロッキング）
- `--formal-timeout=<ms>`: Formalのタイムアウト（GNU timeout があれば適用）
- 非ブロッキング設計
  - fail-fast: setup, qa（ビルド/単体テストの致命的失敗は即終了）
  - warn & continue: spec/sim/coverage/adapters/formal（入力不在はスキップ、要約/検出のみ継続）

## PR サマリ連携（CI/ローカル）
- 生成: `scripts/summary/render-pr-summary.mjs`
  - Coverage: `coverage-summary.json` を表示（artifacts 配下もフォールバック）
  - Adapters: ok/warn/error 集計、検出件数、警告件数、サンプル（最大3件の「adapter: summary」）
  - Formal: aggregate/summary があれば短縮表示（present/ran/ok 等）
- 出力: `artifacts/summary/PR_SUMMARY.md`
- CI では Verify 系ジョブが PR へ Upsert（非ブロッキング）

## アダプタ JSON の軽バリデーション（警告のみ）
- 実施タイミング: Playbook の `detectAdapters` フェーズ
- ルール（最小・warn-only）
  - 共通: `summary` 必須（文字列）、`status` は `ok|warn|warning|error`
  - Lighthouse: `details[]` または `summary` に performance/Perf のヒント
  - AXE: `violations[]` または `summary` に a11y/AXE のヒント
  - Jest/Vitest: `summary` に pass/fail/tests のヒント
  - 不明/推測不能アダプタ: 警告
- 出力: `artifacts/ae/adapters/adapters-validation.json`（report-only）

## CI での使い方（PRコメント/権限）
- 起動（権限不要; PRコメント投稿権限があれば実行）
  - `/verify-lite`（軽量検証）
  - `/run-qa(-dispatch)`, `/run-security(-dispatch)` 等（必要時）
- 取り込み（権限）
  - 通常のMerge: Write 以上
  - 管理者マージ: Admin（要件未達チェックが FAIL の場合でも取り込みたいとき）

## トラブルシュート
- Formal ツール未導入: `status=tool_not_available` でスキップ。導入/環境変数設定後に `--enable-formal` 実行
- coverage-summary 不在: `coverage` フェーズは note 記録のみ。ユニットテストや計測の設定を確認
- アダプタ要約が見つからない: `artifacts/adapters/**/summary.json` などの生成パスを確認
- PR サマリが反映されない: `/verify-lite` を再実行、Actions のログで Upsert 処理を確認

## クイックリファレンス（コマンド）
- セットアップ+軽量: `node scripts/codex/ae-playbook.mjs --resume --skip=formal`
- Formal込み: `node scripts/codex/ae-playbook.mjs --resume --enable-formal --formal-timeout=60000`
- 検出のみ: `node scripts/codex/ae-playbook.mjs --resume --skip=setup,qa,spec,sim,formal`
- npm 補助: `pnpm run codex:run`
- CodeX プリセット（例）: `codex run playbook:light` / `codex run playbook:formal` / `codex run playbook:detect`
