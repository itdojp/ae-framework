# Issue #1225: Security Upgrade Plan (2026-01-06)

## 目的
Code Scanning で指摘されている依存脆弱性に対して、更新方針と作業順序を整理する。

## 現状の依存バージョン（package.json/overrides）
- `@modelcontextprotocol/sdk`: `^1.25.1`
- `glob`: `^10.5.0`
- `js-yaml`: `^4.1.1`
- `esbuild` (pnpm overrides): `0.27.2`

## 最新バージョン確認（2026-01-06 時点）
- `@modelcontextprotocol/sdk`: 最新 `1.25.1`（更新なし）
- `js-yaml`: 最新 `4.1.1`（更新なし）
- `esbuild`: 最新 `0.27.2`（更新なし）
- `glob`: 最新は `13.0.0`（メジャー更新）。10.x の最新は `10.5.0`

## 重点確認ポイント
1. **MCP SDK**: 依存経路・API 互換性の確認（マイナー/メジャー差分）。
2. **glob**: 10.x 系の修正版が取り込めるか（メジャー更新が必要かを確認）。
3. **js-yaml**: 4.1.1 での脆弱性解消可否を確認（必要なら patch 以上）。
4. **esbuild / Go stdlib**: Go stdlib 脆弱性の影響範囲を確認し、必要なら esbuild のバージョンを引き上げる。

## 調査・更新フロー（最小手順）
1. 依存経路の洗い出し
   - `pnpm why <pkg>`
   - `pnpm list <pkg>`
2. CVE 修正バージョンの確認
   - 各 upstream の release notes / security advisory を確認
3. 依存更新案の作成
   - `package.json` の範囲更新
   - `pnpm.overrides` の上書き見直し
4. 影響テスト
   - `pnpm lint` / `pnpm test:fast` / `pnpm test:int` を優先実行
   - CI で `ci-fast` / `verify-lite` の確認

## 進め方（小粒PR案）
- PR-1: `js-yaml` / `glob` の範囲更新（互換性の影響が少ない順）
- PR-2: `@modelcontextprotocol/sdk` の更新（API 差分の確認含む）
- PR-3: `esbuild` の更新（Go stdlib 脆弱性解消の確認）

## メモ
- 更新は **小粒度** に分割し、CI 失敗時の切り戻しを容易にする。
- PR 作成時は SBOM/Code Scanning の差分が確認できるよう、変更点を明記する。
