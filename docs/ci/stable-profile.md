# Stable CI Test Profile

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR 検証向けに決定的かつ高速なテスト実行を提供するプロファイルです。重い/不安定なスイートはラベルやナイトリーに退避します。

- コマンド: `pnpm run test:ci` / `pnpm run test:ci:stable`
- 除外例: `**/system-integration.test.ts`
- ワークフロー: PR は安定サブセット、E2E はラベル `run-e2e` またはスケジュールで実行

This profile provides deterministic, faster test execution suitable for PR verification. Heavy or flaky suites are gated behind labels or nightly jobs.

## Commands
- Full CI config: `pnpm run test:ci`
- Stable subset: `pnpm run test:ci:stable`

`test:ci:stable` currently excludes:
- `**/system-integration.test.ts`

## Usage in Workflows
- For PR workflows aiming for reliability and speed, run `test:ci:stable` or target explicit suites (`test:unit`, `test:int`, `test:a11y`, `test:coverage`).
- Keep Playwright/E2E runs label-gated (`run-e2e`) or scheduled/nightly.

### Flake Diagnostics
- 再実行時にハンドルリークなどを調査したい場合は、`gh run rerun <runId> -e AE_INTEGRATION_TRACE_HANDLES=1` を指定して `why-is-node-running` の詳細ログを取得します（ローカルでは `AE_INTEGRATION_TRACE_HANDLES=1 pnpm test:int`）。  
- 詳細な運用手順は [`docs/testing/integration-runtime-helpers.md`](../testing/integration-runtime-helpers.md) を参照してください。  
- 調査後は必ず環境変数を外し、常時有効化によるログ肥大や CI コスト増を避けます。

## Evolution
- As we identify more flaky suites, we will either stabilize them (preferred) or move them to label/nightly until fixed.
