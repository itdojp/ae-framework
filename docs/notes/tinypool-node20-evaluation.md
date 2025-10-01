# Tinypool + Node.js 20 Fallback Evaluation (2025-10-01)

## 背景
- Node.js 22.19.0 + tinypool (Vitest) の組み合わせで sporadic crash が発生し、CI の `make test-mutation` や `pnpm vitest` の長時間実行が不安定。
- 現状の CI は `ubuntu-24.04` イメージ (Node 22 系) を使用。Docker/Podman 経由の実行では安定するが、ローカルや GitHub Actions の一部ジョブでクラッシュが残る。

## 調査結果
- `package.json` に Node エンジン制約はなし (LTS でも起動可能)。
- `pnpm env use --global 20` で Node 20.x LTS に切り替えても依存の再インストールのみでビルド可能。
- Vitest は `VITEST_POOL_STRATEGY=forks` や `VITEST_POOL_WORKERS=1` を環境変数で調整可能。Node 20 に降格した場合、標準 `threads` でも crash が再現しないことをローカルで確認 (サンプル: EnhancedStateManager test suite)。
- tinypool v1 系では Node 22 での worker 終了イベントが不安定との既知 Issue (#1001) に一致。

## 推奨ステップ
1. **CI ジョブ単位の Node 20 fallback**
   - Verify Lite / mutation quick / make test-mutation を実行するジョブで `setup-node@v4` に `node-version: '20'` を設定。
   - 既存の Node 22 ランナーは他ジョブ (lint/build) で継続利用し、段階的に比較。
2. **環境変数で pool 戦略を固定**
   - `VITEST_POOL_STRATEGY=forks` と `VITEST_POOL_WORKERS=1` を mutation quick 実行時に設定し、tinypool を経由しない構成を用意。
   - Worker 数が必要なケースでは Node 20 + `threads` で再検証してから拡張する。
3. **ローカルドキュメント**
   - `docs/notes/mutation-coverage-plan.md` に Node 20 fallback 手順 (corepack + pnpm env) を追記し、開発者向けに共有。
4. **長期対応**
   - tinypool v2 以降 (Node 22 最適化) へアップデートした後に再度 Node 22 へ戻すかを比較。
   - GitHub Actions で self-hosted runner (Node 20 LTS 固定) を追加するオプションを検討。

## 次のタスク
- Verify Lite workflow に Node 20 fallback を試験導入し、クラッシュが再現しないかを確認 (#1001)。
- mutation quick 実行ジョブに pool 戦略の環境変数を追加し、実行時間への影響を測定。
- Node 22 ランナーでも tinypool v2 / Vitest v3 が安定するか定期的に確認し、報告する。
