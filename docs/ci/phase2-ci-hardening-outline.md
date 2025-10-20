# CI Hardening Phase 2 (Issue #1005)

## 背景
- Phase1（integration cleanup / timeout / retry）は完了済み（PR #1190 merged）。
- Phase2 は Verify Lite を中心とした CI パイプラインの安定化・分割・環境制御を目的とする。
- 現状 Verify Lite ワークフローに多数の smoke / mutation / MBT が詰め込まれており、再試行時に dry-run で失敗しやすい（Stryker quick モードなど）。

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
   - Verify Lite から Integration + Heavy を切り出し、`test:ci:stable`（fast系）と `test:ci:extended`（integration/MBT/mutation）に分割。
   - `test:ci:stable` は PR デフォルト、`test:ci:extended` は label (`run-integration`, `run-mutation`) または nightly へ。
2. **ラベル駆動実行の棚卸し**  
   - `enforce-testing`, `enforce-coverage`, `run-qa`, `run-security` のトリガー先を docs に明記し、ワークフロー側の `if:` 条件を整理。
3. **環境検出ロジック**  
   - Podman/Secrets を必要とするジョブ（コンテナ・security）は forks で失敗しやすい → `if: github.event.pull_request.head.repo.fork == false` 等でガード。
4. **テスト結果キャッシュ検討**  
   - MBT (`artifacts/mbt/summary.json`)、mutation auto diff `reports/mutation/` を再利用できるようにし、再実行時はスキップまたは replay のみ実施。

## 次のアクション候補
1. `docs/ci-policy.md` に CI hardening 方針を追記（テスト分類表、ラベル一覧、再実行時の TRACE_HANDLES / AE_INTEGRATION_RETRY 手順）。  
2. 新ブランチ `feature/ci-hardening-phase2` で以下を順に実装:
   1. `package.json` に `test:ci:extended`（integration + heavy）新設、Verify Lite から heavy ステップを切り出し。
   2. `.github/workflows/verify-lite.yml` を軽量化し、`ci.yml` などに integration/heavy スイートを移行。
   3. ラベル条件を `docs/ci/label-gating.md` と整合させ、CI `if:` 条件を更新。
   4. キャッシュ/再試行手順のガイドを追加し、`docs/testing/integration-runtime-helpers.md` と連携。
3. Mutation auto diff（Stryker quick）用の dry-run 成功条件を改善（workspace tempDir 参照など）し、Verify Lite 再実行時の失敗を減らす。

## 参考リンク
- Issue #1005: Test Stability Issues - Flaky Test Resolution and CI Hardening
- PR #1190: Phase1 completion (integration cleanup helpers)
- docs/testing/integration-runtime-helpers.md: TRACE_HANDLES / AE_INTEGRATION_RETRY 手順
- docs/ci/stable-profile.md: Flake Diagnostics ガイド
