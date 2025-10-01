# Issue Progress Snapshot (2025-09-29)

| Issue | Theme | Status | Latest Notes |
|-------|-------|--------|--------------|
| #997 | Week1: フルパイプライン復元の詳細化 | ⏳ 継続 | Resilience／Telemetry／Property 系の回帰を解消し、Bulkhead 統合テストも通過。`pnpm test:ci` は緑化済み。`PODMAN_COMPOSE_PROVIDER=podman-compose make test-docker-all` の順次成功と Podman 手順整備が完了し、現在は mutation survivor 解消と Verify ワークフロー拡張が主な残課題。|
| #999 | Week2: 継続運用計画の具体化 | ⏳ 継続 | Verify Lite / mutation-quick GitHub Check を整備し、自動チェックステップからレポート取得可能に。mutation quick は `src/api/server.ts` 100% / `src/utils/enhanced-state-manager.ts` 58.33% に到達。Docker 系は Podman compose でグリーン。最新 flake-detection は 5 回走で 0 件（stable）。Verify Lite に加え、`Mutation Quick` ワークフローでも Survived ミュータントを JSON 化して Step Summary / アーティファクトに出力可能にした（既定スコープの workflow_dispatch は TokenOptimizer/Playwright 系テストがベースラインで失敗するため、mutate 指定またはテスト修正が前提）。残課題: Conformance Verification Engine の入力バリデーション強化と Golden 指標再調整。|
| #1001 | Week2 Tracker | ✅ 進捗記録中 | `src/api/server.ts` の Mutation quick を 100% まで引き上げ（span helper 導入で survivor 0）。Resilience/Telemetry/EvidenceValidator の退行も修正済み。tinypool (Node22) の不安定挙動は未解消。|
| #1002 | Week3 準備 (予定) | 💤 未着手 | Week2 の残課題（Docker 実行環境整備・mutation survivors 対応）完了後に着手予定。現時点では準備メモのみ。|
| #1003 | Week3 Tracker | 💤 未着手 | Week3 の進行条件となる CI/テスト基盤の整備待ち。前段となる #999/#1001 の完了がブロッカー。|
|

> 注: ネットワーク制限により GitHub Issue 本体のチェック更新は未実施。上記メモをベースに再接続後 `gh issue edit` で反映予定。

## チェックリスト

### #997 Week1: フルパイプライン復元
- [x] Docker Desktop / Podman のインストールおよび `docker compose` / `podman compose` rootless 動作確認（cgroupfs 設定含む）
- [x] `make test-docker-unit` を実行し成果物を確認（Podman Compose + cgroupfs で 69 ケースがコンテナ内完走）
- [x] `PODMAN_COMPOSE_PROVIDER=podman-compose make test-docker-all` を順次成功まで実行し、ログとレポートを `docs/notes/full-pipeline-restore.md` に反映

### #999 Week2: 継続運用計画
- [ ] Verify Lite / mutation-quick GitHub Check の動作確認（オンライン復旧後）
- [x] Docker ベース e2e ターゲット（integration/e2e/performance）の成果物取得（Podman compose で全サービス成功。flakedetection レポートは別タスクで分析）
- [x] Flake detection コンテナの `consistently-failing` レポート解析と環境要因の洗い出し（最新サマリは flake 0 件を確認）
- [x] Mutation サバイバー整理計画の策定（#1001 から移管）
- [x] Resilience / Telemetry / EvidenceValidator のユニット退行修正（`tests/resilience/backoff-strategies`, `timeout-patterns`, `tests/telemetry/runtime-guards`, `tests/utils/evidence-validator` を再整備）

### #1001 Week2 Tracker
- [x] 予約キャンセルフローと各種テスト資産の実装
- [x] Mutation quick (API server 100% / EnhancedStateManager 58.33%) の結果ドキュメント化
- [ ] EnhancedStateManager 残存ミュータント（`versionIndex` / `stateImported` / `findKeyByVersion`）に対するテスト実装
- [ ] tinypool クラッシュ回避策の検証（Node 20 切替または Vitest 設定調整）
- [x] ResilientHttpClient / IntelligentTestSelection / EvidenceValidator のテスト修正と再実行

### #1002 Week3 準備
- [x] Docker/Podman 環境整備完了の確認（Podman rootless + compose ログを docs に記録）
- [ ] Mutation サバイバー残課題 (#999/#1001) の解消
- [ ] Week3 用 Verify Lite / Docker ジョブ計画書の作成
- [x] Bulkhead / Property テストの期待値見直しと `pnpm test:ci` 成功条件の整理（前倒し検討）

### #1003 Week3 Tracker
- [ ] Week3 着手条件（Docker runtime, tinypool 安定化, Mutation 整理）の完了確認
- [ ] Week3 で実施するフルパイプライン実行手順のドラフト作成
- [ ] Issue コメントへ最新進捗と次アクションを反映（オンライン復旧後）
