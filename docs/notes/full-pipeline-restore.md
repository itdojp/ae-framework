# Week1: フルパイプライン復元メモ

## ブランチ/ベースコミット
- 作業ブランチ: `revive/full-pipeline`
- ベースコミット: `f912e11a8e24211e06d3c711d18a2e056cca5020`
- GNU Make 4.3 でターゲット名にコロンが使えなかったため、`test:docker` などはハイフン区切りに改名済み。

## Makefile タスク実行結果（2025-Week2 更新）
| コマンド | 結果 | 備考 |
|----------|------|------|
| `make spec-lint` | ✅ | `.spectral.yaml` / `.gherkin-lintrc` を追加し、OpenAPI に `servers`・`tags`・レスポンス本文を補完して Spectral + Gherkin Lint を通過。 |
| `make formal-check` |✅| `scripts/formal/run-apalache.sh` で Apalache v0.50.3 をローカルキャッシュし、`Inventory.tla` を再構成して invariant 検証が成功。 |
| `make test-acceptance` |✅| Cucumber ステップを Fastify + in-memory サービスに接続し、5 シナリオ（16 ステップ）が HTTP レベルで成功。 |
| `make test-property` |✅| `tests/property` 用 Vitest プロジェクトを新設し、Reservation スキーマを Fast-check で検証。 |
| `make test-mbt` |✅| `tests/mbt/run.js` を復元し、モデルベーステストで在庫遷移ロジックを確認。 |
| `make test-mutation` | ⚠️ | 限定スコープ（`src/api/server.ts`, `src/utils/enhanced-state-manager.ts`, `src/domain/**`）で約 35 分。Quick モードは API server **100%** / EnhancedStateManager **58.33%**（survived 102 / no-cover 23 / errors 49）。`versionIndex` 更新・`stateImported` イベント・`findKeyByVersion` ガードのサバイバーが残課題。
| `make test-contract` |✅| `scripts/pipelines/run-pact-contracts.mjs` が Fastify プロバイダを起動しつつ Pact CLI で契約群を検証。複数 JSON（`PACT_CONTRACTS` で絞り込み可能）に対応。 |
| `make test-api-fuzz` |✅| Podman + Schemathesis コンテナで実行成功。Fastify スタブを OpenAPI と揃えた在庫初期化／検証に刷新し、警告ゼロで完走。 |
| `make policy-test` |✅| `scripts/policy/ensure-opa.sh` で OPA v1.9.0 をローカルキャッシュし、Rego テスト 3 件が通過。 |
| `make sbom` |✅| `syft scan dir:.` で CycloneDX JSON を生成し、`security/sbom/sbom.json` に保存（Makefile でキャッシュ済み）。 |
| `make verify-trace` |✅| `scripts/verify/traceability.sh` が `traceability.csv` を出力。 |
| `make test-docker-unit` | ✅ | `PODMAN_COMPOSE_PROVIDER=podman-compose` で実行し、Vitest 69 ケースがコンテナ内で成功。rootless Podman は `cgroupfs` マネージャーで稼働。後片付け時に存在しないコンテナの警告が出るが無害。|
| `make test-docker-all` | ✅ | `PODMAN_COMPOSE_PROVIDER=podman-compose` で unit → integration → e2e → quality → flake → performance を順次実行し exit 0 を確認。テアダウン時の「コンテナが存在しない」警告は未起動サービスを指すため無害。レポートは `reports/` 以下に保存。|

## 今回追加・復旧した主な成果物
- `scripts/formal/run-apalache.sh`: Apalache のオンデマンドダウンロードと実行ラッパー。
- `specs/formal/tla+/Inventory.tla` / `Inventory.cfg`: Apalache で検証可能な形へ再定義。
- `.spectral.yaml` / `.gherkin-lintrc`: OpenAPI & BDD lint 用設定。
- `specs/openapi/api.yaml`: Lint を通すための `servers`・`tags`・レスポンス詳細を補強。
- `specs/bdd/features/reservations.feature` / `specs/bdd/steps/reservations.steps.js`: Fastify を介した受け入れテストを実現。
- `tests/property/*`・`tests/mbt/run.js`: Property / MBT 検証の再構築。
- `tsconfig.stryker.json`・`stryker.config.js`・`vitest.stryker.config.ts`: Stryker + TypeScript Checker を限定構成で再有効化。
- `scripts/pipelines/run-pact-contracts.mjs`・`contracts/reservations-consumer.json`: Pact CLI によるローカル契約検証フロー。
- `docs/infra/container-runtime.md`: Podman / Docker いずれにも対応するセットアップガイド。

## Week2 追加メモ（2025-Week2）

### PnPM コマンド整備 (2025-10-09)
- `pnpm pipelines:pact`: Pact Provider Verifier を pnpm 単体で実行し、`scripts/pipelines/run-pact-contracts.mjs` を通じて複数契約を検証します。
- `pnpm pipelines:api-fuzz`: Schemathesis ベースの API fuzz を pnpm コマンド化し、Podman/Docker なしでもローカルで再現可能にします。
- `pnpm pipelines:mutation:quick` / `pipelines:mutation:enhanced`: mutation quick ランを pnpm から直接呼び出し、`--mutate` オプションを `--` 以降で渡せるようにしました。
- `pnpm pipelines:full`: verify:lite → Pact → API fuzz → mutation quick を順次呼び出す統合ドライバー。`--skip=pact` や `--mutation-target=src/utils/enhanced-state-manager.ts` で柔軟に制御できます。

### CI 組み込みメモ (2025-10-09)
- `scripts/pipelines/run-full-pipeline.mjs` はステップごとの開始・終了ログを出力し、Verify Lite の Step Summary に転記しやすい形式を維持します。
- GitHub Actions では `pnpm pipelines:full --skip=api-fuzz` といった形でジョブを段階的に分割し、負荷の高いステップはラベルベースで opt-in する運用を想定しています。
- mutation quick は `pipelines:mutation:enhanced` を使うことで EnhancedStateManager を 10〜12 分で再計測でき、Week3 以降のレポート復旧要件を満たします。


## Week3 完了見通し
- Mutation quick / Verify Lite auto-diff 連携は完了。残る Week3 課題は mutation の残存 CompileError 監視と Verify Lite 拡張フェーズ（lint/spec/property/MBT/Pact）の本格導入。
- Docker 系タスクは `PODMAN_COMPOSE_PROVIDER=podman-compose make test-docker-all` が順次成功。各サービスのレポート確認と flake 判定結果の分析（reports/flake-detection/**）が次ステップ。

- Scoped Stryker quick モード (2025-09-30) は約 6 分で完走し、mutation score **100.00%**（survived 0 / errors 25 / no-cov 0）を記録。`recordSpanMetrics` / `recordSpanError` helper と追加ユニットテストで span 関連ミュータントを完全に除去。
- 直前の通常スコープ実行 (2025-09-28) では mutation score **92.52%**（survived 19 / no-cov 0 / errors 16）。残課題は `user-agent` の trim／`startTime` フォールバックなど (#1002)。
- `scripts/mutation/run-scoped.sh` は quick / auto-diff オプションを実装済みで、JSON/HTML レポートを `reports/mutation/` に保存。Verify Lite からも呼び出し済み。
- TypeScript の型エラー（`code-generation-agent.ts` など 6 箇所）を解消し、Stryker の TypeScript Checker が通る状態を維持。
- `make test-api-fuzz` は Podman + Schemathesis コンテナで警告ゼロまで改善。API スタブの初期化とバリデーションを OpenAPI と整合。
- `make test-mutation` は限定スコープ構成で約 35 分。今後は Quick モード結果を基準に対象拡大を検討。
- `make test-docker-unit` が Podman Compose でビルド＆実行できるようになった（現状 Vitest の対象が少ないため追加テストを検討）。
- `scripts/policy/ensure-opa.sh` で OPA v1.9.0 をキャッシュし `make policy-test` が 3 ケース通過。
- `make sbom` は `syft scan dir:.` を使って CycloneDX JSON を生成する構成へ更新。
- `pnpm test:unit` に InventoryService / EnhancedStateManager / API server など 80+ ケースのユニットテストを追加し、CI でも安定して走行。

## 残課題とバックログ候補
1. **Apalache ワークフローの一般化** – 今回はローカル実行で通ったが、CI 共有キャッシュやバージョン固定を整理する。
2. **Mutation テストのカバレッジ改善** – Quick モードは API server 100% / EnhancedStateManager 58.33%（survivor 102）。`versionIndex` 更新・`stateImported` イベント・`findKeyByVersion` ガードの追加テストが必要。
3. **Contract テストの拡充** – Pact Provider Verifier を複数契約に適用できるよう、状態セットアップや CI 連携を検討する。
4. **コンテナ運用テストの拡張** – `PODMAN_COMPOSE_PROVIDER=podman-compose make test-docker-all` は順次成功。flake detection レポートの自動集計と安定性モニタリングを継続。
5. **Policy / SBOM の CI 組み込み** – ローカルでは OPA/ Syft が通るようになったので、CI キャッシュ・成果物の保管/署名ポリシーを整備する。
6. **End-to-End サンプルの拡張** – Property / MBT / BDD / Pact を単一シナリオ上で連携させ、フルパイプラインのデモを整備する。（進捗: shared fixture 実装済 / Pact 複数契約追加済）

## Week5 プラン草案 (2025-10-09)
- Verify Lite main job: `pnpm verify:lite` + mutation summary (必須)
- Optional heavy gate: `pnpm pipelines:full --skip=api-fuzz` (nightly) / `--skip=verify:lite` (mutation focused)
- Dashboard 集約: Tempo / Grafana ノートを `docs/trace/tempo-dashboard-notes.md` へ移行し、Step3 完了後に CI export を紐付け
- Artifact 整理: Pact / API fuzz / Mutation / Projector / Validator の結果を `artifacts/full-pipeline/<step>/` に格納
- 成果報告: Week5 終了時に #997 本体へダイジェスト（Verify Lite サマリ + Mutation トレンド + Trace dashboard スクリーンショット）を投稿

## 次のアクション候補
- `docs/infra/container-runtime.md` を参照し、Podman もしくは Docker Compose を稼働させた上で `make test-docker-unit` / `make test-docker-all` の依存コンテナとネットワークを整備する。
- Stryker 用 `tsconfig.stryker.json` の対象を徐々に拡大し、Mutation スコアとテストカバレッジを改善する計画を Issue 化する。
- Mutation クイックランに `--auto-diff` を組み込み、差分ファイルのみを対象にしたサニティ実行を Verify Lite から呼べるよう CI へ取り込む。
- Pact 契約のカバレッジを追加し、契約テストの結果を自動レポートするワークフローを整備する。

### Flake detection (2025-09-30)
- 旧ツールが `npm test` を呼び出していたため全試行が 415 (環境エラー) で失敗。`scripts/flake-detector.js` を `pnpm test:ci` ベースに更新し、`FLAKE_COMMAND`/`FLAKE_ARGS` で上書き可能にした。
- `test-flake-detection` はコンテナ内で実行できるようになったが、`reports/flake-detection/` への書き込み権限が無いと `EACCES` で失敗するため、Makefile で事前に `mkdir` + `chmod` を実施するよう更新。
- Podman rootless 実行では、ホスト側の `reports/flake-detection` を write 可能にしておくこと。`make test-docker-flake` 実行時は権限調整後にレポート出力まで完了する。
- 最新の `flake-summary-latest.md` は flake 0 件（stable）を報告。旧 JSON の `consistently-failing` は修正前の履歴であり、Issue #999 に検証メモを残した。
