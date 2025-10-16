# Issue Progress Snapshot (2025-10-08)

| Issue | Theme | Status | Latest Notes |
|-------|-------|--------|--------------|
| #997 | Week1: フルパイプライン復元の詳細化 | ⏳ 継続 | Podman/Compose 手順と `make test-docker-all` は安定。mutation survivor の整理と Verify Lite ⇔ フルパイプライン連携の再整備が残課題。Spec ビルド sparse checkout やローカルアクション不足による失敗は解消済み。|
| #999 | Week2: 継続運用計画の具体化 | ⏳ 継続 | Verify Lite / mutation-quick GitHub Check は main へ復帰済み。TokenOptimizer quick は 64.78% → 100%（PR #1091）、EnhancedStateManager quick は 64.78%（survived 243）。Step Summary/Artifact 再出力とラベル運用の本格化が残タスク。|
| #1001 | Week2 Tracker | ✅ 進捗記録中 | API server mutation スコア 100% を維持しつつ、TokenOptimizer/CircuitBreaker PBT 安定化 (#1091) を完了。EnhancedStateManager survivor (`versionIndex` / `stateImported` / `findKeyByVersion`) 対策と tinypool 障害調査が継続タスク。2025-10-09: versionIndex 連番確認と findKeyByVersion の正パス検証を unit test で補強。|
| #1002 | Week3 準備 (予定) | 💤 未着手 | Week2 の残課題（EnhancedStateManager survivor、Verify Lite lint backlog）を整理した後に着手予定。Trace ダッシュボード案と Docker ジョブ計画書のドラフト化が必要。|
| #1003 | Week3 Tracker | 💤 未着手 | Week3 着手条件（Docker runtime, tinypool 安定化, mutation 整理）が揃っていないため、Issue コメントと手順書は更新保留。|
|
> メモ内容は GitHub Issues (#997, #999, #1001, #1002, #1003) にもコメントとして反映済み（2025-10-08 更新）。

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
- [x] Verify Lite / mutation-quick GitHub Check の動作確認（PR #1093 + `pnpm pipelines:full` でローカル再現可能）
- [x] Docker ベース e2e ターゲット（integration/e2e/performance）の成果物取得（Podman compose で全サービス成功。flakedetection レポートは別タスクで分析）
- [x] Flake detection コンテナの `consistently-failing` レポート解析と環境要因の洗い出し（最新サマリは flake 0 件を確認）
- [x] Mutation サバイバー整理計画の策定（#1001 から移管）
- [x] Resilience / Telemetry / EvidenceValidator のユニット退行修正（`tests/resilience/backoff-strategies`, `timeout-patterns`, `tests/telemetry/runtime-guards`, `tests/utils/evidence-validator` を再整備）

### #1001 Week2 Tracker
- [x] 予約キャンセルフローと各種テスト資産の実装
- [x] Mutation quick (API server 100% / EnhancedStateManager 67.90%) の結果ドキュメント化
- [x] EnhancedStateManager 残存ミュータント（`versionIndex` / `stateImported` / `findKeyByVersion`）に対するテスト実装（PR #1094 / 2025-10-09: 連番バージョン検証テストを追加）
- [x] tinypool クラッシュ回避策の検証（Node 20 fallback + Vitest forks 戦略を導入済み）
- [x] ResilientHttpClient / IntelligentTestSelection / EvidenceValidator のテスト修正と再実行

### #1002 Week3 準備
- [x] Docker/Podman 環境整備完了の確認（Podman rootless + compose ログを docs に記録）
- [x] Mutation サバイバー残課題 (#999/#1001) の解消（EnhancedStateManager quick 72.02% まで回復）
- [x] Week3 用 Verify Lite / Docker ジョブ計画書の作成（`docs/notes/full-pipeline-restore.md` に pnpm パイプライン案を追記）
- [x] Bulkhead / Property テストの期待値見直しと `pnpm test:ci` 成功条件の整理（前倒し検討）

### #1003 Week3 Tracker
- [ ] Week3 着手条件（Docker runtime, tinypool 安定化, Mutation 整理）の完了確認
- [x] Week3 で実施するフルパイプライン実行手順のドラフト作成（`scripts/pipelines/run-full-pipeline.mjs` とドキュメントの組み合わせ）
- [ ] Issue コメントへ最新進捗と次アクションを反映（オンライン復旧後）
