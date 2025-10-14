# Verify Lite Lint Backlog (2025-10-04)

## 集計ハイライト
- `VERIFY_LITE_ENFORCE_LINT=1 pnpm run verify:lite` → 2,641 件（107 errors, 2,534 warnings）。
- 上位カテゴリ（`scripts/ci/verify-lite-lint-summary.mjs` より）:
  1. `@typescript-eslint/no-unsafe-*` 系（1,371 件） — 主に `src/cegis/auto-fix-engine.ts`, `src/utils/quality-policy-loader.ts`。
  2. `@typescript-eslint/no-explicit-any`（648 件） — 同上。
  3. `@typescript-eslint/require-await`（209 件） — `src/analysis/dependency-analyzer.ts`, `src/cegis/auto-fix-engine.ts`。

## 対応ロードマップ
1. **Phase A (verify-lite hardening)**
   - [ ] `src/analysis/dependency-analyzer.ts`: async メソッドを sync 化 or `Promise.resolve()` 化、`any` の明示的型付け。
   - [ ] `src/cegis/auto-fix-engine.ts`: activity log / pattern 集計部を型定義化し、`require-await` を解消。
     - [x] `analyzeFailurePatterns` / `generateRecommendations` を同期化し、`RepairAction` 型を適用。
   - [ ] `src/utils/quality-policy-loader.ts`: Policy JSON 型を整備、unsafe assignment を解消。
2. **Phase B (CI gating)**
   - [ ] verify-lite lint を `VERIFY_LITE_ENFORCE_LINT=1` で定期実行し、総件数を Step Summary に表示。
   - [ ] 主要ディレクトリの lint 修正が完了した段階で label `lint-strict` を導入。
   - [ ] ラベル `enforce-verify-lite-lint` を付与した PR は `VERIFY_LITE_ENFORCE_LINT=1` を強制し、baseline 超過でジョブを失敗させる運用ドキュメントを整備（付与権限、解除フロー、再実行手順を明文化）。
3. **Phase C (Strict by default)**
   - [ ] 全カテゴリが許容値（< 50 件）になったら verify-lite lint 失敗をブロッキング化。

## Issue 連携
- Issue #1012 Phase A: `docs/notes/pipeline-baseline.md` の手順に従い、Verify Lite ローカル実行ログ（lint サマリ・mutation survivors）を保存し、進捗報告に添付する。
- Issue #1016 Lint/Muation backlog:
  - [ ] 上記 Phase A タスクが完了したら survivors 上位 10 件を再計測し、Issue コメントに貼り付ける。
  - [ ] Mutation Quick（59.74% → 65% 以上）が達成できたら Phase B へ移行する旨を更新。
  - [ ] Lint suppression の恒久対応（型定義追加 or アーキテクチャ整理）が必要な場合は、Issue 内で新規サブタスクに分解して記録する。

## ログ保存ポリシー
- `VERIFY_LITE_KEEP_LINT_LOG=1` で `pnpm run verify:lite` を実行し、生成された `verify-lite-lint-summary.json` / `verify-lite-lint.log` を `reports/verify-lite/<timestamp>/` に保管する。
- Mutation Quick を併走させる場合は `VERIFY_LITE_RUN_MUTATION=1` を指定し、`reports/mutation/survivors.json` と `reports/mutation/summary.json` を同一ディレクトリに移動する（Phase A の進捗エビデンスとして必須）。
- CI の Step Summary とローカルログの内容が乖離した場合は、Issue #1016 のコメントに原因と対処方針を追記する。
- `verify-lite-run-summary.json` に各ステップの成功/失敗が出力されるため、Issue への報告時は JSON の添付または主要ステータスの抜粋を行う。
- `config/verify-lite-lint-baseline.json` に基準値を保存し、`enforce-verify-lite-lint` ラベル付き PR では Verify Lite ワークフローが基準超過時に失敗するように構成されている。

## 参考
- lint サマリは `verify-lite-lint-summary.json`（artifact）に保存。
- `docs/notes/pipeline-baseline.md` に最新ステータスを反映。
