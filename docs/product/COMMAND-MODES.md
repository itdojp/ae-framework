# ae-framework コマンド体系（実行モード別）

> Language / 言語: English | 日本語

---

## English (Summary)

This document explains the recommended command entrypoints for development, distribution, and CI, and clarifies when to use `pnpm run`, `pnpm exec`, or direct scripts.

---

## 日本語

## 1. 目的
ae-framework は **複数の実行モード**（開発/配布/CI）を持ちます。  
本書では「どの入口を使うべきか」を **用途別に一本化** し、手戻りを防ぎます。

## 2. 実行モードの全体像

| モード | 推奨入口 | 主な用途 | 備考 |
| --- | --- | --- | --- |
| 開発（TS実行） | `pnpm run ae-framework -- <cmd>` | CLIの挙動確認、機能開発 | `src/cli/index.ts` を直接実行 |
| 配布/ビルド後 | `pnpm exec ae <cmd>` | 利用者向けCLI | `package.json bin` が `dist/src/cli/*` を指す |
| CI | `pnpm run <script>` | verify-lite / test / security 等 | GitHub Actions が主に使用 |
| 直接スクリプト | `node scripts/*` | メンテ/高度運用 | ドキュメントに明記された場合のみ推奨 |

## 3. 開発時の推奨入口（TypeScript）

```bash
pnpm run ae-framework -- --help
pnpm run ae-framework -- spec --help
pnpm run ae-framework -- quality run --env development
```

## 4. 配布/ビルド後の推奨入口

```bash
pnpm run build
pnpm exec ae --help
pnpm exec ae spec --help
```

## 5. CIでの推奨入口

CIは `pnpm run <script>` を前提に設計されています。

```bash
pnpm run verify:lite
pnpm run test:fast
pnpm run security:integrated:quick
```

## 6. よくある混乱と解消

### 6.1 `spec validate` の入力指定
`spec validate` は **`-i` が必須** です（`src/cli/spec-cli.ts` の `requiredOption`）。

```bash
pnpm run spec:validate -i spec/example-spec.md --output .ae/ae-ir.json
```

### 6.2 `help` の表示
`pnpm run help` は `scripts/project/help.mjs` を実行し、**script群の一覧**を表示します。  
一方、`pnpm run ae-framework -- --help`（または `pnpm exec ae --help`）は **CLIのサブコマンド** を案内します。

## 7. 例外: 直接スクリプトを使う場合
以下のように **ドキュメントで指示されている場合のみ** 直叩きを許容します。

```bash
# 例: 重い検証のキャッシュ/トレンド比較
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

## 8. 関連資料
- 利用マニュアル: `docs/product/USER-MANUAL.md`
- 典型的な利用シナリオ: `docs/product/USE-CASES.md`
- CLIリファレンス: `docs/reference/CLI-COMMANDS-REFERENCE.md`
