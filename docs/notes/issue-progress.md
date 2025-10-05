# Issue Progress Snapshot (2025-10-04)

| Issue | Theme | Status | Latest Notes |
|-------|-------|--------|--------------|
| #997 | Week1: フルパイプライン復元の詳細化 | ⏳ 継続 | Resilience／Telemetry／Property 系の回帰を解消し、Bulkhead 統合テストも通過。`pnpm test:ci` は緑化済み。`PODMAN_COMPOSE_PROVIDER=podman-compose make test-docker-all` の順次成功と Podman 手順整備が完了し、現在は mutation survivor 解消と Verify ワークフロー拡張が主な残課題。|
| #999 | Week2: 継続運用計画の具体化 | ⏳ 継続 | Verify Lite / mutation-quick GitHub Check を整備済み。TokenOptimizer quick run は 100% を維持。EnhancedStateManager quick run は rollback 系テスト追加後も **59.74%**（survived 184）で頭打ち。Podman unit compose は `AE_HOST_STORE` キャッシュ導入で 45 秒程度まで短縮。残課題はトランザクション／スナップショット／復元系のサバイバー解消。|
| #1001 | Week2 Tracker | ✅ 進捗記録中 | `src/api/server.ts` の Mutation quick を 47%→67%→81%→88%→94%→98.69%→100% まで引き上げ。TokenOptimizer quick は 32.12%、EnhancedStateManager quick は rollback/initalize/legacy Buffer テスト追加後も **59.74%**（survived 184）。イベント/rollback 付近のフォローアップを継続する。|
| #1002 | Week3 準備 (予定) | 💤 未着手 | Week2 の残課題（Docker 実行環境整備・mutation survivors 対応）完了後に着手予定。現時点では準備メモのみ。|
| #1003 | Week3 Tracker | 💤 未着手 | Week3 の進行条件となる CI/テスト基盤の整備待ち。前段となる #999/#1001 の完了がブロッカー。|
|

> メモ内容は GitHub Issues (#997, #999, #1001, #1002, #1003) にもコメントとして反映済み（2025-10-04 更新）。

### Latest PR / Follow-ups
- Podman/WSL ランタイム最適化: PR [#1014](https://github.com/itdojp/ae-framework/pull/1014)
- Spec generate/model gating: PR [#1023](https://github.com/itdojp/ae-framework/pull/1023) — `.github/workflows/spec-generate-model.yml` introduces drift fail-fast + KvOnce property run
- Spec trace conformance gating: PR [#1024](https://github.com/itdojp/ae-framework/pull/1024) — adds KvOnce trace validation job + NDJSON schema docs
- OTLP trace conversion: PR [#1025](https://github.com/itdojp/ae-framework/pull/1025) — adds OTLP→NDJSON converter + workflow integration
 - OTLP trace conversion: PR [#1025](https://github.com/itdojp/ae-framework/pull/1025) — adds OTLP→NDJSON converter + workflow integration
- ネイティブ compose 検証: Issue [#1015](https://github.com/itdojp/ae-framework/issues/1015)
- Mutation survivor 削減タスク: Issue [#1016](https://github.com/itdojp/ae-framework/issues/1016)
## Pipeline Health (2025-10-04)
- `pnpm vitest run --reporter dot` はベンチマーク／AE-IR suite の再有効化と ResilientHttpClient の Promise Rejection 警告解消により全 suite 緑化済み。
- `scripts/docker/run-unit.sh` は PATH から `/mnt/c/` を除外し Podman rootless を想定。事前に `pnpm fetch --prefer-offline` でホスト側 `.pnpm-store/` をウォームアップし、compose は `podman` / `podman-compose` いずれでも 600 秒タイムアウト付きで実行。エラー検知後は即座に `pnpm exec vitest run tests/unit` へフォールバックするため長時間ハングが消滅。

### Podman compose troubleshooting
- `>>>> Executing external compose provider "podman-compose"` が表示された場合は native compose (`PODMAN_COMPOSE_PROVIDER=podman`) で再試行し、`podman ps` と `podman system info` が成功するか確認する。
- `/mnt/c/` を含む PATH で実行すると外部 docker-compose.exe が呼び出されるため、`export PATH="$(printf '%s' "$PATH" | tr ':' '\n' | grep -v '^/mnt/c/' | paste -sd:)"` で一時的に除外する。
- 共有ストアは `AE_HOST_STORE` で指定し、デフォルトはレポジトリ直下の `.pnpm-store/`。CI では `$GITHUB_WORKSPACE/.pnpm-store`（目安 2〜3 GB）をキャッシュし、compose 実行は最大 600 秒（タイムアウト）を基準に設計する。


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
