---
docRole: derived
canonicalSource:
- docs/reference/CLI-COMMANDS-REFERENCE.md
- scripts/project/help.mjs
lastVerified: '2026-03-22'
---
# ae-framework コマンド体系（実行モード別）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
`ae-framework` has multiple execution modes for development, packaged distribution, and CI. This document fixes the recommended entrypoint for each mode so operators do not mix development shims, packaged CLI binaries, and direct scripts.

### 2. Execution Mode Matrix
| Mode | Recommended entrypoint | Main purpose | Notes |
| --- | --- | --- | --- |
| Development (TypeScript) | `pnpm run ae-framework -- <cmd>` | feature work, command validation, local debugging | runs `src/cli/index.ts` directly |
| Benchmark compatibility | `pnpm exec tsx src/cli.ts bench` | legacy `benchmark-report/v1` compatibility | legacy shim; do not use for new user-facing flows |
| Packaged / built CLI | `pnpm exec ae <cmd>` | end-user operation after build | `package.json bin` points to `dist/src/cli/*` |
| CI | `pnpm run <script>` | `verify-lite`, tests, security, automation | GitHub Actions uses this path by default |
| Direct scripts | `node scripts/*` | maintenance or advanced operational tasks | only when the document explicitly calls for it |

### 3. Development Entry Point
The canonical development-time CLI entrypoint is `src/cli/index.ts`. The benchmark-specific `src/cli.ts` remains a legacy compatibility shim and is not the place to add new user-facing commands.

Example:
```bash no-doctest
pnpm run ae-framework -- --help
pnpm run ae-framework -- spec --help
pnpm run ae-framework -- quality run --env development
```

### 4. Packaged / Built Entry Point
Use the packaged binaries only after a build.

```bash no-doctest
pnpm run build
pnpm exec ae --help
pnpm exec ae spec --help
```

### 5. CI Entry Point
CI is designed around `pnpm run <script>`.

```bash no-doctest
pnpm run verify:lite
pnpm run test:fast
pnpm run security:integrated:quick
```

On `main`, the typical required-check baseline remains `verify-lite`, `policy-gate`, and `gate`.

### 6. Common Confusions
#### 6.1 `spec validate` input handling
`spec validate` requires `-i` because `src/cli/spec-cli.ts` declares it as a required option.

```bash no-doctest
pnpm run spec:validate -i spec/example-spec.md --output .ae/ae-ir.json
```

#### 6.2 `help` output
`pnpm run help` executes `scripts/project/help.mjs` and prints repository script groups. `pnpm run ae-framework -- --help` or `pnpm exec ae --help` shows CLI subcommands instead.

### 7. When direct scripts are acceptable
Direct script execution is acceptable only when the document explicitly instructs it, such as heavy-test caching or trend comparison.

```bash no-doctest
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

### 8. Related Documents
- `docs/product/USER-MANUAL.md`
- `docs/product/USE-CASES.md`
- `docs/reference/CLI-COMMANDS-REFERENCE.md`

---

## 日本語

## 1. 目的
ae-framework は **複数の実行モード**（開発/配布/CI）を持ちます。  
本書では「どの入口を使うべきか」を **用途別に一本化** し、手戻りを防ぎます。

## 2. 実行モードの全体像

| モード | 推奨入口 | 主な用途 | 備考 |
| --- | --- | --- | --- |
| 開発（TS実行） | `pnpm run ae-framework -- <cmd>` | CLIの挙動確認、機能開発 | `src/cli/index.ts` を直接実行 |
| ベンチマーク互換 | `pnpm exec tsx src/cli.ts bench` | `benchmark-report/v1` の既存互換生成 | legacy compatibility shim。新規導線では非推奨 |
| 配布/ビルド後 | `pnpm exec ae <cmd>` | 利用者向けCLI | `package.json bin` が `dist/src/cli/*` を指す |
| CI | `pnpm run <script>` | verify-lite / test / security 等 | GitHub Actions が主に使用 |
| 直接スクリプト | `node scripts/*` | メンテ/高度運用 | ドキュメントに明記された場合のみ推奨 |

## 3. 開発時の推奨入口（TypeScript）

メインCLIの canonical entrypoint は `src/cli/index.ts` です。<br>
ベンチマークの user-facing 入口は `src/cli/benchmark-cli.ts`（`ae-benchmark`）で、`src/cli.ts` は既存の `benchmark-report/v1` 互換を維持する legacy shim としてのみ扱います。

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
