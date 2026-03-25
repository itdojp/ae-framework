---
docRole: ssot
lastVerified: '2026-03-25'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# CI Documentation Boundary Matrix

> Language / 言語: English | 日本語

---

## English

Update summary: 2026-03-25

Purpose: define responsibility boundaries for `docs/ci` operational documents so guidance stays deduplicated and the current escalation path remains clear.

For the agent-document boundary on the CI side, see `docs/agents/agents-doc-boundary-matrix.md`.

### Boundary definition (primary docs vs. focused runbooks)

| Category | Primary document | Supporting runbooks / references | Managed scope |
| --- | --- | --- | --- |
| Global policy | `docs/ci-policy.md` | `docs/ci/workflow-role-matrix.md`, `docs/ci/OPT-IN-CONTROLS.md` | required checks, opt-in labels, dispatch policy |
| Daily operations | `docs/ci/ci-operations-handbook.md` | `docs/ci/ci-troubleshooting-guide.md` | monitoring, rerun, stop/recovery standard procedures |
| PR automation | `docs/ci/pr-automation.md` | `docs/ci/copilot-review-gate.md`, `docs/ci/copilot-auto-fix.md`, `docs/ci/auto-merge.md`, `docs/ci/change-package.md` | Copilot review gate, auto-fix, auto-merge, Change Package |
| Docs verification | `docs/ci/docs-doctest-policy.md` | `scripts/ci/check-docs-doctest-policy-sync.mjs` | docs-doctest execution boundary and sync check |
| Failure handling | `docs/ci/automation-failure-policies.md` | `docs/ci/automation-rollback-runbook.md`, `docs/ci/automation-alerting.md` | fail-open / fail-closed, rollback, notifications |

### Deduplication rules

1. Consolidate policy in `docs/ci-policy.md` and execution procedures in `docs/ci/ci-operations-handbook.md`.
2. Do not restate detailed troubleshooting in `docs/ci-policy.md`; link to the relevant runbook instead.
3. Keep the CI entrypoint link set in `docs/README.md` and `docs/ci-policy.md` aligned.
4. Enforce CI entrypoint consistency with `pnpm run check:ci-doc-index-consistency`.

## 日本語

最終更新: 2026-03-25

目的: `docs/ci` 配下の運用ドキュメントについて、重複を抑えた責務境界を定義する。

Agent文書側の境界定義は `docs/agents/agents-doc-boundary-matrix.md` を参照。

### 境界定義（主文書と個別runbook）

| 区分 | 正式な主文書 | 補助runbook / 関連資料 | 管理対象 |
| --- | --- | --- | --- |
| 全体方針 | `docs/ci-policy.md` | `docs/ci/workflow-role-matrix.md`, `docs/ci/OPT-IN-CONTROLS.md` | Required checks / opt-in labels / dispatch方針 |
| 日次運用 | `docs/ci/ci-operations-handbook.md` | `docs/ci/ci-troubleshooting-guide.md` | 監視・再実行・停止/復帰の標準手順 |
| PR自動化 | `docs/ci/pr-automation.md` | `docs/ci/copilot-review-gate.md`, `docs/ci/copilot-auto-fix.md`, `docs/ci/auto-merge.md`, `docs/ci/change-package.md` | Copilot review gate / auto-fix / auto-merge / Change Package |
| Docs検証 | `docs/ci/docs-doctest-policy.md` | `scripts/ci/check-docs-doctest-policy-sync.mjs` | docs-doctest 実行境界と同期チェック |
| 障害対応 | `docs/ci/automation-failure-policies.md` | `docs/ci/automation-rollback-runbook.md`, `docs/ci/automation-alerting.md` | fail-open/fail-closed, rollback, 通知 |

### 重複削減ルール

1. 方針は `docs/ci-policy.md` に集約し、実行手順は `docs/ci/ci-operations-handbook.md` へ集約する。
2. `docs/ci-policy.md` には詳細トラブルシュートを再掲せず、該当runbookへのリンクを置く。
3. `docs/README.md` と `docs/ci-policy.md` のCI導線は、同一の必須リンク集合を維持する。
4. CI導線の整合は `pnpm run check:ci-doc-index-consistency` で機械検証する。
