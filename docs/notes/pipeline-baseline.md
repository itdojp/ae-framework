# Pipeline Baseline (2025-10-04)

## 目的
- 仕様 → テスト → コード → 検証 → 運用 まで "最低限通しで動作する" フローを明文化し、Issue #1012 Phase A の足場とする。
- 手元および CI で再現できるコマンド群を整理し、未整備の部分は課題として切り出す。

## 実行環境メモ
- OS: WSL2 (Ubuntu 22.04)
- Node: v22.x (pnpm `corepack enable` で取得)
- Podman: rootless / `podman-compose` (Python 実装) をフォールバックで利用
- `AE_HOST_STORE`: リポジトリ直下 `.pnpm-store/`

## コマンドヘルス一覧
| 区分 | コマンド | 最終確認 | 結果 | 備考 |
|------|----------|----------|------|------|
| Unit | `pnpm vitest run tests/unit/utils/enhanced-state-manager.test.ts tests/unit/utils/enhanced-state-manager.rollback.test.ts --reporter dot` | 2025-10-04 | ✅ | EnhancedStateManager 系 49 ケースがローカルで緑化。ログは `reports/unit-20251004.log` に保存予定 (TODO)。 |
| Unit (Docker) | `AE_HOST_STORE=$(pwd)/.pnpm-store scripts/docker/run-unit.sh` | 2025-10-04 | ✅ | Podman フォールバックで 83 ケースが約 45s で完走。`podman compose -f` 非対応時は `podman-compose` に自動切替。 |
| Mutation (Quick) | `STRYKER_TIME_LIMIT=480 ./scripts/mutation/run-scoped.sh --quick -m src/utils/enhanced-state-manager.ts -c configs/stryker.enhanced.config.js` | 2025-10-04 | ⚠️ | score 59.74% / survived 184。`calculateChecksum` / `reviveEntryData` 周辺が要追加テスト (Issue #1016)。 |
| Verify Lite | `pnpm run verify:lite` | 2025-10-04 | ✅ | ローカルスクリプト追加済。TypeScript エラーを解消し exit 0 を確認（lint は非強制のため警告のみ出力）。実行前に `.stryker-tmp` を自動削除するよう対応。 |
| Make targets | `make test-*` 系 | 未 | ⛔ | ルートに Makefile が存在せず、直近のテーブルは `docs/notes/full-pipeline-restore.md` の古い情報。Phase A で Makefile 復元可否を調査する。 |
| CI | `.github/workflows/pr-verify.yml` | 2025-10-04 | ✅ | Podman cache 導入の PR #1014 でローカル確認。CI 側での成功は PR マージ後に要確認。 |
| CI | `.github/workflows/ci.yml` | 2025-10-04 | ⚠️ | pnpm cache を追加。現状の main ブランチでの成功状況は未確認。CI 再実行後にログをレビューする。 |

### 未検証だが Phase A で確認が必要なコマンド
- `pnpm run test:fast` / `pnpm run test:int`
- `pnpm run mutation` (フルスコープ)
- `pnpm run spec:lint` / `pnpm run spec:check` (該当スクリプト要調査)
- `scripts/ci/verify-lite-demo.sh`

### Verify Lite lint（enforce モード）の現状
- `VERIFY_LITE_ENFORCE_LINT=1 pnpm run verify:lite` で lint を強制すると 2,653 件（107 errors, 2,546 warnings）が検出される。
- 主なカテゴリ:
  - `@typescript-eslint/no-unused-vars`（例: `src/analysis/dependency-analyzer.ts`, `src/cegis/auto-fix-engine.ts`）
  - `@typescript-eslint/require-await`（同上）
  - `@typescript-eslint/no-explicit-any` / `no-unsafe-assignment` / `no-unsafe-member-access`（`src/utils/quality-policy-loader.ts` ほか）
  - `no-useless-escape` / `require-await`（`src/utils/token-optimizer.ts`）
- lint を必須にするには大規模なリファクタが必要。短期的には lint をレポート用途に留め、改善タスクを段階的に切り出す方針が現実的。
- `.github/workflows/verify-lite.yml` で lint 出力を `verify-lite-lint-summary.json` に集計し、Step Summary に上位ルールを出力する処理を追加済み（artifact も併せて保存）。
- `scripts/ci/verify-lite-lint-summary.mjs` で出力を集計し、`artifacts/verify-lite-lint-summary.json` に上位ルール（例: `@typescript-eslint/no-unsafe-*` 1371 件、`@typescript-eslint/no-explicit-any` 648 件、`@typescript-eslint/require-await` 209 件）を記録。

## 既存ドキュメント
- `docs/notes/full-pipeline-restore.md`: revive/full-pipeline ブランチ時の Make 実行結果。現状との乖離があるため差分確認が必要。
- `docs/infra/container-runtime.md`: Podman / Docker のセットアップ手順。今回の run-unit.sh 改修と整合済み。

## TODO (Phase A 対応)
1. **Makefile** の所在調査（削除 or 置き換え状況の確認）→ Commit `676b64ab9c00`（2025-08-22）で全削除済み。Make ターゲットは pnpm スクリプト・GitHub Actions に置き換えられているため、復元には新規設計が必要。
2. `pnpm run verify:lite` の実行可否を確認 → package.json にスクリプトが存在せず `ERR_PNPM_NO_SCRIPT`。代替フロー（verify-lite.yml をローカル再現するスクリプト）を検討。
3. 最小サンプルシナリオ（仕様→テスト→コード→運用）の候補を確定し、`docs/samples/minimal-run.md` を作成 ✔️
4. 上記サンプルを CI（pr-verify or 新規ワークフロー）へ組み込むための要件を整理（下記参照）

### CI 組み込み要件（ドラフト）
- ワークフロー名: `minimal-pipeline.yml`（仮）
- トリガー: pull_request / manual dispatch
- ステップ案:
  1. `pnpm run build`
  2. `CODEX_SKIP_QUALITY=1 CODEX_TOLERANT=1 pnpm run codex:quickstart`
  3. `pnpm vitest run --project unit --reporter dot`
  4. `STRYKER_TIME_LIMIT=480 ./scripts/mutation/run-scoped.sh --quick -m src/utils/enhanced-state-manager.ts -c configs/stryker.enhanced.config.js`（オプション）
  5. アーティファクト: `artifacts/codex-quickstart-summary.md`, `tests/api/generated/**`, mutation レポート
- 必要な環境変数: `AE_HOST_STORE=$GITHUB_WORKSPACE/.pnpm-store`
- キャッシュ: `.pnpm-store`（既存の actions/cache を再利用）
- 既知の課題: Quality Gate ポリシー未整備、Makefile 欠落、mutation survivors（Issue #1016）

### Minimal Pipeline Workflow（実装済み）
- `.github/workflows/minimal-pipeline.yml` を作成（manual dispatch 専用）。
  - CodeX quickstart（品質ゲートスキップ）、EnhancedStateManager ユニットテスト、verify-lite（lint サマリ出力）、KvOnce TLC を順次実行。
  - `VERIFY_LITE_ENFORCE_LINT` を入力で切り替え可能。
  - `scripts/ci/verify-lite-lint-summary.mjs` により lint 結果を `verify-lite-lint-summary.json` として保存し、Step Summary へ上位ルールを表示。
- 今後: 差分 mutation quick の実行や生成アーティファクト比較を統合予定。

## 参考ログ
- `logs/run-unit-20251004.txt`: Podman 実行ログ（`scripts/docker/run-unit.sh`）※未保存
- `reports/mutation/mutation.json|html`: 直近の mutation quick 結果 (score 59.74%)

## lint backlog ドキュメント
- `docs/notes/verify-lite-lint-plan.md`: verify-lite lint 集計と段階的対応計画を整理。
