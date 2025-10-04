# Minimal Pipeline Run (Spec → Tests → Code → Verify → Operate)

## ゴール
- 手元で "仕様→生成→検証" の一連の流れを再現する。
- Issue #1012 Phase A のサンプルとして、CI でも同手順を実行できるよう準備する。

## 前提
- Node 22 / pnpm 10 (`corepack enable` 済み)
- 依存インストール: `pnpm install`
- CLI ビルド済み: `pnpm run build`

## 手順

1. **品質ゲートをスキップして Quickstart を実行**
   ```bash
   CODEX_SKIP_QUALITY=1 CODEX_RUN_FORMAL=1 CODEX_TOLERANT=1 pnpm run codex:quickstart
   ```
   - `CODEX_SKIP_QUALITY=1`: 現状 `quality-policy.json` に `Code Linting` / `Test-Driven Development` 閾値が未登録で失敗するため一時的にスキップ。
   - `CODEX_RUN_FORMAL=1`: TLA+ と OpenAPI を生成し、契約テンプレートも出力する。
   - `CODEX_TOLERANT=1`: 警告を許容し exit code=0 を保証。

2. **生成物を確認**
   - `artifacts/codex/quickstart-formal.tla`
   - `artifacts/codex/quickstart-openapi.yaml`
   - `tests/api/generated/` (契約・E2E テンプレート)
   - `artifacts/codex-quickstart-summary.md`

3. **ユニットテストで生成コードを検証**
   ```bash
   pnpm vitest run tests/unit/utils/enhanced-state-manager.test.ts tests/unit/utils/enhanced-state-manager.rollback.test.ts --reporter dot
   ```
   - EnhancedStateManager の初期化・ロールバック・TTL 分岐を網羅。

4. **Podman コンテナ内でユニットテスト（任意）**
   ```bash
   AE_HOST_STORE=$(pwd)/.pnpm-store scripts/docker/run-unit.sh
   ```
   - `podman compose -f` 非対応環境では `podman-compose` に自動フォールバック。

5. **KvOnce TLA+ PoC の確認（任意）**
   ```bash
   pnpm run spec:kv-once:tlc
   pnpm run spec:kv-once:apalache   # Apalache が導入済みの場合
   ```
   - 実行結果は `hermetic-reports/formal/kvonce-*-summary.json` に保存されます（minimal pipeline でも取得）。

6. **Mutation quick（任意）**
   ```bash
   STRYKER_TIME_LIMIT=480 ./scripts/mutation/run-scoped.sh --quick -m src/utils/enhanced-state-manager.ts -c configs/stryker.enhanced.config.js
   ```
   - 現状スコア 59.74%（survived 184）。Issue #1016 にて改善予定。

## 既知の課題 / TODO
- `CODEX_SKIP_QUALITY=1` を外すと `Quality gate 'Code Linting' not found in policy` で失敗。ポリシー更新が必要。
- Makefile が欠落しており、`make verify-lite` 等は利用不可。旧記録は `docs/notes/full-pipeline-restore.md` 参照。
- `pnpm run verify:lite` は TypeScript エラーを解消済。実行時に `.stryker-tmp` を自動削除し、lint 警告は非強制でログのみ出力される。
- 生成された契約テンプレートを実際に実行するコマンドが未整備。CI 組み込み時に要検討。

## CI への組み込みドラフト
1. `pnpm run build`
2. `CODEX_SKIP_QUALITY=1 CODEX_TOLERANT=1 pnpm run codex:quickstart`
3. `pnpm vitest run --project unit --reporter dot`
4. 生成物 (`artifacts/codex-quickstart-summary.md`, `tests/api/generated/**`) を artifact としてアップロード

上記が安定した後に Verify Lite や Mutation quick の実行を追加していく。
