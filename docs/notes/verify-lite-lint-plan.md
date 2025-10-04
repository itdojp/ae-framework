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
   - [ ] `src/utils/quality-policy-loader.ts`: Policy JSON 型を整備、unsafe assignment を解消。
2. **Phase B (CI gating)**
   - [ ] verify-lite lint を `VERIFY_LITE_ENFORCE_LINT=1` で定期実行し、総件数を Step Summary に表示。
   - [ ] 主要ディレクトリの lint 修正が完了した段階で label `lint-strict` を導入。
3. **Phase C (Strict by default)**
   - [ ] 全カテゴリが許容値（< 50 件）になったら verify-lite lint 失敗をブロッキング化。

## 参考
- lint サマリは `verify-lite-lint-summary.json`（artifact）に保存。
- `docs/notes/pipeline-baseline.md` に最新ステータスを反映。
