---
docRole: ssot
lastVerified: '2026-03-25'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Docs Doctest Policy

This document defines the operating policy for the docs doctest lanes that protect Markdown quality in PRs and scheduled runs. / 本ドキュメントは、PR と定期実行で Markdown 品質を保護する docs doctest レーンの運用方針を定義します。

> Language / 言語: English | 日本語

---

## English

### Purpose

- keep PR-time documentation validation fast and deterministic
- separate full-repository doctest coverage into a scheduled lane without losing regression visibility

### Execution scope

| Lane | Trigger | Execution |
| --- | --- | --- |
| `doctest-index` | `pull_request` / `push(main)` / `workflow_dispatch` | `check-doc-consistency-all` plus doctest for README.md and docs/README.md; on `pull_request`, changed Markdown files are also validated |
| `doctest-full` | `schedule` / `workflow_dispatch(full=true)` | full doctest for `docs/**/*.md` |

Workflow: `.github/workflows/docs-doctest.yml`

### Operating rules

1. Use the index lane as the default PR guard to minimize review latency.
2. Run the full lane on the weekly schedule to detect broad regressions.
3. When a maintainer needs a full result immediately, rerun via `workflow_dispatch` with `full=true`.
4. Run `scripts/ci/check-docs-doctest-policy-sync.mjs` first so workflow/package-script/policy drift is caught before the doctest step.
5. Docs governance, contract catalog validation, and generated agent-command sync are aggregated into the same lane through `check-doc-consistency-all.mjs`.
6. When a governance change or front matter update pulls additional Markdown into changed-files scope, reproduce the changed-Markdown doctest locally before opening or updating the PR.
7. Use `text` fences for illustrative snippets, sample output, and pseudo payloads. Use `no-doctest` only when the language tag itself must be preserved.

### Failure response runbook

1. Identify the failed job: `doctest-index` or `doctest-full`.
2. Classify the failure from the log.
   - `Code blocks`: fix the corresponding fenced block in the Markdown file.
   - `Invalid Links`: repair the target path or update the URL.
3. Reproduce locally.
   - index failure: `DOCTEST_ENFORCE=1 pnpm run test:doctest:index`
   - changed-Markdown failure: `DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main`
   - full failure: `DOCTEST_ENFORCE=1 pnpm run test:doctest:full`
4. If the failing block is explanatory only, convert it to `text`. If the language marker must remain visible, add a modifier such as ```` ```typescript no-doctest ````.
5. After the fix, either rerun failed jobs in the same run or push a follow-up commit to trigger the lane again.

### Local reproduction commands

```bash
node scripts/ci/check-docs-doctest-policy-sync.mjs
pnpm run check:doc-consistency
pnpm run check:ci-doc-index-consistency
DOCTEST_ENFORCE=1 pnpm run test:doctest:index
DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main
DOCTEST_ENFORCE=1 pnpm run test:doctest:full
```

## 日本語

### 目的

- PR のドキュメント検証を短時間で安定実行する
- 全量ドキュメント検証を定期実行に分離し、検証品質を維持する

### 実行スコープ

| レーン | トリガ | 実行内容 |
| --- | --- | --- |
| `doctest-index` | `pull_request` / `push(main)` / `workflow_dispatch` | `check-doc-consistency-all` + README.md / docs/README.md の doctest。`pull_request` では差分 Markdown も追加検証 |
| `doctest-full` | `schedule` / `workflow_dispatch(full=true)` | `docs/**/*.md` の全量 doctest |

Workflow: `.github/workflows/docs-doctest.yml`

### 運用ルール

1. PR では index スコープを基本とし、レビュー待ち時間を抑える
2. 全量チェックは週次 schedule で実行し、広域回帰を検知する
3. 全量結果の確認が必要な場合は `workflow_dispatch` で `full=true` を指定して再実行する
4. `scripts/ci/check-docs-doctest-policy-sync.mjs` を先行実行し、workflow / package script / policy の整合ドリフトを早期検出する
5. docs governance / contract catalog / generated agent commands sync は `check-doc-consistency-all.mjs` 経由で同じレーンに集約する
6. doc governance 拡張や front matter 追加で markdown を changed-files 対象へ入れる場合は、PR 前に changed-markdown doctest をローカルで再現する
7. 説明用 snippet / 出力例 / 擬似 payload は `text` fence を基本とし、言語情報を残したい場合のみ `no-doctest` modifier を明示する

### 失敗時の対応手順（runbook）

1. 失敗ジョブを特定する（`doctest-index` / `doctest-full`）
2. ログから失敗種別を確認する
   - `Code blocks` の失敗: 該当 Markdown のコードブロックを修正
   - `Invalid Links` の失敗: リンク先の修正または URL 更新
3. ローカル再現する
   - index 失敗時: `DOCTEST_ENFORCE=1 pnpm run test:doctest:index`
   - changed-markdown 失敗時: `DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main`
   - full 失敗時: `DOCTEST_ENFORCE=1 pnpm run test:doctest:full`
4. 失敗した code block が説明用であれば `text` へ変更する。言語情報を残したい場合は ```` ```typescript no-doctest ```` のように modifier を付ける
5. 修正後、同一 run の `Re-run failed jobs` か、PR へ追 commit を push して再実行する

### ローカル実行コマンド

```bash
node scripts/ci/check-docs-doctest-policy-sync.mjs
pnpm run check:doc-consistency
pnpm run check:ci-doc-index-consistency
DOCTEST_ENFORCE=1 pnpm run test:doctest:index
DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main
DOCTEST_ENFORCE=1 pnpm run test:doctest:full
```
