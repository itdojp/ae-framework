---
docRole: ssot
lastVerified: '2026-03-25'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# CI Baseline Checklist

> Language / 言語: English | 日本語

---

## English

This checklist provides the minimum baseline checks for confirming CI health without running heavy suites.

### When to use
- After CI pipeline changes
- After dependency updates
- When flaky test volume increases

### Baseline checks (minimum)
- Verify Lite is green
- Lint/type/coverage steps pass
- Required gate jobs are green

### Commands
- `pnpm run verify:lite`
- `pnpm run test:ci:lite`

### CI notes
- Heavy suites are label-gated (see `docs/ci/label-gating.md`)
- Prefer stable profile for baseline signal (`docs/ci/stable-profile.md`)

### Failure triage
- Use `docs/testing/flaky-test-triage.md` for reproduction and isolation
- Refer to `docs/testing/test-categorization.md` to pick the right suite
- Keep a short log in `docs/notes/pipeline-baseline.md` when investigating

## 日本語

本チェックリストは、重い suite を実行せずに CI baseline の健全性を確認するための最小確認項目を定義します。

### 使う場面

- CI pipeline を変更した後
- dependency 更新の後
- flaky test の発生量が増えた時

### Baseline checks（最小）

- Verify Lite が green であること
- lint / type / coverage 系の step が通っていること
- Required gate job が green であること

### コマンド

- `pnpm run verify:lite`
- `pnpm run test:ci:lite`

### CI 運用メモ

- 重い suite は label-gated 運用とする（`docs/ci/label-gating.md` を参照）
- baseline signal には安定系 profile（`docs/ci/stable-profile.md`）を優先する

### 失敗時の切り分け

- 再現と切り分けは `docs/testing/flaky-test-triage.md` を参照する
- どの suite を使うべきかは `docs/testing/test-categorization.md` を参照する
- 調査時は `docs/notes/pipeline-baseline.md` に短い調査ログを残す
