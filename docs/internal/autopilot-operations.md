# Autopilot Operations Runbook

## 目的
watcher / ブリッジ / Autopilot を安全に停止・再開するための運用手順をまとめる。
単一 CodeX 運用時の干渉回避を目的とする。

補足:
- GitHub Actions 側の opt-in 実装として `Codex Autopilot Lane`（`.github/workflows/codex-autopilot-lane.yml`）を追加。
- 運用の主眼は同じ（停止条件の明確化と fail-closed）だが、外部常駐スクリプトではなく PR 単位の workflow 実行で管理する。

## 停止（干渉防止）
- watcher を停止（各ワークスペースで実行中の `watch.sh` を終了）
- Autopilot 停止:
  - `pkill -f '~/work/CodeX/ae/codex-autopilot.sh' || true`
- READY の新規付与を控える（watcher が拾うため）

## 再開（必要時）
- watcher 再開（各エージェントのワークスペース）
  - `WATCH_INTERVAL=30 ./watch.sh`
- Autopilot 再開（in-progress Issue を対象）
  - `export GH_REPO=itdojp/ae-framework`
  - 各ワークスペースで `source agent.env; ~/work/CodeX/ae/codex-autopilot.sh <issue#> >/dev/null 2>&1 & disown`
- READY を段階的に付与（流量調整）

## ブリッジ / Autopilot の要点
- ブリッジ（Zellij向け）: `~/work/CodeX/ae/bridge-codex-relay-zellij.sh`
  - Zellij の `codex-<role>` セッションで CodeX Pane がフォーカス前提
  - プロンプト投入後に Enter を自動送信
- Autopilot: `~/work/CodeX/ae/codex-autopilot.sh`
  - 既定: `INTERVAL=60s` / `COOLDOWN=180s` / `MAX_FEEDS=240`
  - 停止条件: `status:review`, `status:done`, `status:blocked`, `autopilot:off`
  - ラベルでテンポ制御: `autopilot:fast`（最短30s）/ `autopilot:slow`（3倍）
  - 直近の Issue 活動があればクールダウン内は投下しない（スパム抑止）

## ラベル/コマンド運用（覚書）
- ステータス: `status:ready` / `status:in-progress` / `status:review` / `status:blocked` / `status:done`
- 役割: `role:*`、スプリント: `sprint:*`、Epic: `epic:#*`
- スラッシュコマンド（Issue コメントのみ）:
  - `/start` `/ready-for-review` `/assign` `/handoff` `/plan`

## 監視
- サマリ: `~/work/CodeX/ae/telemetry/status-board.sh --watch 10`
- イベント追尾: `~/work/CodeX/ae/telemetry/status-board.sh --events-follow`
- ログ/ステータス/イベント: `~/work/CodeX/ae/telemetry/{logs,status,events.ndjson}`
