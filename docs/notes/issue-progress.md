# Issue Progress Snapshot (2025-10-06)

| Issue | Theme | Status | Latest Notes |
|-------|-------|--------|--------------|
| #997 | Week1: フルパイプライン復元の詳細化 | ⏳ 継続 | Resilience／Telemetry／Property 系の回帰を解消し、Bulkhead 統合テストも通過。`pnpm test:ci` は緑化済み。`PODMAN_COMPOSE_PROVIDER=podman-compose make test-docker-all` の順次成功と Podman 手順整備が完了し、現在は mutation survivor 解消と Verify ワークフロー拡張が主な残課題。Fail-Fast Spec ビルドの sparse checkout を調整し、ローカルアクション不足で落ちる事象を解消。|
<<<<<<< HEAD
| #999 | Week2: 継続運用計画の具体化 | ⏳ 継続 | Verify Lite / mutation-quick GitHub Check を整備済み。TokenOptimizer quick run は 100% を維持。EnhancedStateManager quick run は logicalKey 欠落・TTL 未指定・object 圧縮パス等のテスト拡充で **71.15%**（killed 328 / survived 133）を記録。Podman unit compose は `AE_HOST_STORE` キャッシュ導入で 45 秒程度まで短縮。`scripts/ci/run-verify-lite-local.sh` の追加に加え、`scripts/trace/run-kvonce-trace-replay.mjs` でトレース検証→TLC リプレイを自動化。残課題は versionIndex 周りのサバイバーと Verify Lite のラベル制御の本運用化。|
| #1001 | Week2 Tracker | ✅ 進捗記録中 | `src/api/server.ts` の Mutation quick を 47%→67%→81%→88%→94%→98.69%→100% まで引き上げ。TokenOptimizer quick は 32.12%、EnhancedStateManager quick は import/gc/index テスト＋論理キー/TTL ガードで **71.15%**（survived 133）。性能プロジェクトは `vitest --passWithNoTests` 化してゲート継続、イベント/rollback 付近のフォローアップを継続する。Trace まわりは Projector/Validator/OTLP 変換の CLI テストと conformance 連結テストを追加済み。|
=======
| #999 | Week2: 継続運用計画の具体化 | ⏳ 継続 | Verify Lite / mutation-quick GitHub Check を整備済み。TokenOptimizer quick run は 100% を維持。EnhancedStateManager quick run は import 系テスト追加で **72.02%**（killed 332 / survived 129）まで向上。Podman unit compose は `AE_HOST_STORE` キャッシュ導入で 45 秒程度まで短縮。`scripts/ci/run-verify-lite-local.sh` の追加に加え、`scripts/trace/run-kvonce-trace-replay.mjs` でトレース検証→TLC リプレイを自動化。残課題はトランザクション／rollback 系サバイバーと Verify Lite のラベル制御の本運用化。|
| #1001 | Week2 Tracker | ✅ 進捗記録中 | `src/api/server.ts` の Mutation quick を 47%→67%→81%→88%→94%→98.69%→100% まで引き上げ。TokenOptimizer quick は 32.12%、EnhancedStateManager quick は import/gc テスト追加で **72.02%**（survived 129）。性能プロジェクトは `vitest --passWithNoTests` 化してゲート継続、イベント/rollback 付近のフォローアップを継続する。Trace まわりは Projector/Validator/OTLP 変換の CLI テストと conformance 連結テストを追加済み。|
>>>>>>> 9cf6584 (test: capture missing key/version import cases)
| #1002 | Week3 準備 (予定) | 💤 未着手 | Week2 の残課題（Docker 実行環境整備・mutation survivors 対応）完了後に着手予定。現時点では準備メモのみ。|
| #1003 | Week3 Tracker | 💤 未着手 | Week3 の進行条件となる CI/テスト基盤の整備待ち。前段となる #999/#1001 の完了がブロッカー。|
|

> メモ内容は GitHub Issues (#997, #999, #1001, #1002, #1003) にもコメントとして反映済み（2025-10-06 更新）。

### Latest PR / Follow-ups
- Podman/WSL ランタイム最適化: PR [#1014](https://github.com/itdojp/ae-framework/pull/1014)
- Spec generate/model gating: PR [#1023](https://github.com/itdojp/ae-framework/pull/1023) — `.github/workflows/spec-generate-model.yml` introduces drift fail-fast + KvOnce property run
- Spec trace conformance gating: PR [#1024](https://github.com/itdojp/ae-framework/pull/1024) — merged。KvOnce trace validation job + NDJSON schema docsが main に反映済み。
- OTLP trace conversion: PR [#1025](https://github.com/itdojp/ae-framework/pull/1025) — merged。OTLP→NDJSON converter + workflow integration が landing。
- Grafana Tempo dashboard note: PR [#1052](https://github.com/itdojp/ae-framework/pull/1052) — TraceQL クエリ/属性確認手順を追記。
- GC logging coverage: PR [#1054](https://github.com/itdojp/ae-framework/pull/1054) — EnhancedStateManager の TTL 失効ログをテスト化。
- Import edge-case coverage: PR [#1055](https://github.com/itdojp/ae-framework/pull/1055) — compressed Buffer／checksum フォールバックのテスト追加、mutation score 67.90%。
- ネイティブ compose 検証: Issue [#1015](https://github.com/itdojp/ae-framework/issues/1015)
- Mutation survivor 削減タスク: Issue [#1016](https://github.com/itdojp/ae-framework/issues/1016)
## Pipeline Health (2025-10-05)
- `pnpm vitest run --reporter dot` はベンチマーク／AE-IR suite の再有効化と ResilientHttpClient の Promise Rejection 警告解消により全 suite 緑化済み。性能プロジェクトが test ファイル未配置でも `--passWithNoTests` で exit 0 を維持。
- `scripts/docker/run-unit.sh` は PATH から `/mnt/c/` を除外し Podman rootless を想定。事前に `pnpm fetch --prefer-offline` でホスト側 `.pnpm-store/` をウォームアップし、compose は `podman` / `podman-compose` いずれでも 600 秒タイムアウト付きで実行。エラー検知後は即座に `pnpm exec vitest run tests/unit` へフォールバックするため長時間ハングが消滅。SBOM/Drift check は CLI bin の実行権限補正後に再実行予定。

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
- [x] Mutation quick (API server 100% / EnhancedStateManager 67.90%) の結果ドキュメント化
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
