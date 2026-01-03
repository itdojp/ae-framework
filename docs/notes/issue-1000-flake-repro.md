# Issue 1000: Flake 再現チェックリスト

Integration テストの flake を再現・固定するための最小手順を整理します。詳細なヘルパー利用法は `docs/testing/integration-runtime-helpers.md` を参照してください。

## 目的
- 再現条件を固定し、失敗パターン（タイミング / リソース / クリーンアップ）を切り分ける
- flake detection のログとローカル再現を同じ条件で揃える

## 最小手順
1. **実行条件を記録**
   - commit / runner OS / Node / pnpm / `AE_INTEGRATION_RETRY` / `AE_INTEGRATION_TRACE_HANDLES`
2. **再現確認（全体）**
   - `AE_INTEGRATION_RETRY=1 pnpm test:int`
3. **ハンドルリーク調査（詳細）**
   - `AE_INTEGRATION_TRACE_HANDLES=1 pnpm test:int`
4. **対象テストの絞り込み**
   - `pnpm test:int -- --testNamePattern "<name>"`
5. **flake detection の再現**
   - `pnpm flake:detect:quick`（必要なら `--runs`/`--threshold` を調整）

## 記録テンプレート
- commit:
- runner OS:
- Node / pnpm:
- 実行コマンド:
- `AE_INTEGRATION_RETRY`:
- `AE_INTEGRATION_TRACE_HANDLES`:
- 失敗テスト名:
- 失敗ログの要点:

## 参照
- `docs/testing/integration-runtime-helpers.md`
- `scripts/flake-detector.js`
