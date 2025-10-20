# CI Hardening Phase 2 （Issue #1005）

## 背景
- Phase1 （integration cleanup / timeout / retry）は完了済み （PR #1190 merged）。
- Phase2 は Verify Lite を中心とした CI パイプラインの安定化・分割・環境制御を目的とする。
- 現状 Verify Lite ワークフローに多数の smoke / mutation / MBT が詰め込まれており、再試行時に dry-run で失敗しやすい （Stryker quick モードなど）。

## 現状のテスト分類
| 種別 | npm script / workflow | 備考 |
|------|----------------------|------|
| Fast / deterministic | `pnpm test:unit`, `pnpm test:fast`, `pnpm test:fast:plus` | Vitest workspace 導入により `vitest.workspace.ts` 切替可能 |
| Integration (slow) | `pnpm test:int`, `pnpm pipelines:pact` | Verify Lite でも実行。mutation auto diff 初期 dry-run 依存 |
| Heavy (mutation / MBT) | `pnpm test:mbt`, mutation auto diff (stryker quick) | Verify Lite 専用ステップとして存在 |
| Property-based / replay | `pnpm test:property`, `pnpm test:replay` | ラベル `enforce-testing` で厳格化可能 |
| Quality / golden | `pnpm test:quality`, `pnpm test:golden` | ラベルゲートで逐次厳格化 |
| Coverage | `pnpm test:coverage:ci` | `coverage` ジョブ独立 |

## 課題整理
1. **テスト分類の明確化とワークフロー分割**  
   - Verify Lite から Integration + Heavy を切り出し、`test:ci:lite` （fast系）と `test:ci:extended` （integration/MBT/mutation）に分割。
   - `test:ci:lite` は PR デフォルト、`test:ci:extended` は label (`run-integration`, `run-mutation`) または nightly へ。
2. **ラベル駆動実行の棚卸し**  
   - `enforce-testing`, `enforce-coverage`, `run-qa`, `run-security` のトリガー先を docs に明記し、ワークフロー側の `if:` 条件を整理。
3. **環境検出ロジック**  
   - Podman/Secrets を必要とするジョブ（コンテナ・security）は forks で失敗しやすい → `if: github.event.pull_request.head.repo.fork == false` 等でガード。
4. **テスト結果キャッシュ検討**  
   - MBT (`artifacts/mbt/summary.json`)、mutation auto diff `reports/mutation/` を再利用できるようにし、再実行時はスキップまたは replay のみ実施。

## 実装状況（2025-10-20）
- [x] `test:ci:lite` / `test:ci:extended` スクリプトを追加し、Verify Lite （安定系）と拡張テストの入口を分離。
- [x] `.github/workflows/verify-lite.yml` から Property / MBT / Pact / Mutation ステップを削除し、軽量ジョブとして再構成。
- [x] `.github/workflows/ci-extended.yml` を新設。`run-ci-extended` / `run-integration` / `run-property` / `run-mbt` / `run-mutation` ラベルで PR から opt-in 実行でき、main push / schedule では自動実行。
- [x] Mutation auto diff / property / MBT サマリを新ワークフローに移設し、従来のレポート （survivors, summary）を維持。
- [x] テストスイートの Stryker/CI セーフ化 （tmpfs ヘルパー導入・Vitest conservative モード追加）。`CI=1 pnpm vitest run tests --pool=forks --watch=false --reporter=dot` と `CI=1 pnpm run test:ci:extended` （mutation quick 含む）が完走 （mutation score 100%、静的ミュート警告あり）。

## 次のアクション候補
1. [ ] `docs/ci-policy.md` / `docs/ci/label-gating.md` を刷新し、新ラベルと実行モード （stable vs extended）を明文化。  
2. [ ] キャッシュ／再実行ガイドを整備し、MBT や mutation サマリの再利用手順を `docs/testing/integration-runtime-helpers.md` に反映。  
3. [ ] Mutation auto diff （Stryker quick） のワークスペース制御を見直し、dry-run 時の一時ディレクトリ競合を解消。  
4. [ ] Nightly での `ci-extended` 成果物 （survivors / MBT summary）を自動比較し、トレンド可視化を導入。  
5. [ ] Mutation quick で報告された静的ミュート （23件）への対応 （`ignoreStatic` 等）を検討し、実行時間の最適化とレポート品質の向上を図る。  

## 参考リンク
- Issue #1005: Test Stability Issues - Flaky Test Resolution and CI Hardening
- PR #1190: Phase1 completion (integration cleanup helpers)
- docs/testing/integration-runtime-helpers.md: TRACE_HANDLES / AE_INTEGRATION_RETRY 手順
- docs/ci/stable-profile.md: Flake Diagnostics ガイド
