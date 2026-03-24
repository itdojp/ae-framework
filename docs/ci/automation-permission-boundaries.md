---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Automation Permission Boundaries

This document defines the permission boundaries for PR automation workflows triggered from `workflow_dispatch`, `issue_comment`, `pull_request`, `pull_request_review`, and `schedule`. / PR自動化ワークフローにおける `workflow_dispatch` / `issue_comment` / `pull_request` / `pull_request_review` / `schedule` 起点の権限境界を整理します。

> Language / 言語: English | 日本語

---

## English

Primary sources:
- `.github/workflows/agent-commands.yml`
- `.github/workflows/copilot-review-gate.yml`
- `.github/workflows/codex-autopilot-lane.yml`
- `.github/workflows/pr-ci-status-comment.yml`
- `.github/workflows/copilot-auto-fix.yml`

### 1. Permission boundary matrix

| Workflow | Trigger | Boundary condition | Intent |
| --- | --- | --- | --- |
| agent-commands (`copilot-review-gate dispatch`) | `issue_comment` | requires a comment attached to a PR plus `github-actions[bot]` and `<!-- AE-COPILOT-AUTO-FIX v1 -->` marker | prevent arbitrary comment-driven dispatch |
| Copilot Review Gate (`gate`) | `workflow_dispatch` | on the default branch, manual runs must provide `pr_number`; otherwise the gate skips or errors | prevent accidental execution against unrelated branches |
| Copilot Auto Fix | `pull_request_review` | excludes fork PRs, limits actors to Copilot identities, and respects the global kill switch | constrain write permission and apply authority |
| Codex Autopilot Lane | `issue_comment` | requires `/autopilot run` on a PR comment from a privileged actor (`MEMBER` / `OWNER` / `COLLABORATOR`) plus the global kill switch guard | prevent automatic updates from arbitrary user comments |
| Codex Autopilot Lane | `pull_request` | requires a non-fork PR with the `autopilot:on` label plus the global kill switch guard | prevent autopilot execution on forks or unlabeled PRs |
| Codex Autopilot Lane | `workflow_dispatch` | requires `pr_number` input plus the global kill switch guard | prevent operators from accidentally targeting the wrong PR |
| PR Maintenance (`update-branch`, `enable-auto-merge`) | `pull_request` / `workflow_dispatch` / `schedule` | excludes fork PRs for PR-origin runs, defaults `workflow_dispatch` `mode` to `both` unless narrowed by the operator, and respects the global kill switch | prevent unnecessary updates or auto-merge enablement |

### 2. Implementation notes

- the global kill switch (`AE_AUTOMATION_GLOBAL_DISABLE`) is enforced in automation lanes that mutate or dispatch follow-up work (`Codex Autopilot Lane`, `PR Maintenance`, `Copilot Auto Fix`); `Copilot Review Gate` does not currently use that kill switch
- `issue_comment` entrypoints must first prove that the comment is attached to a PR, then add actor or marker validation where required
- `workflow_dispatch` entrypoints must require or default critical inputs such as `pr_number` or `mode` so operators do not accidentally target the wrong PR or lane

### 3. Test policy

The minimum boundary regression coverage is implemented in `tests/unit/ci/workflow-permission-boundary.test.ts`.

- verify that workflow definitions still contain the required guard expressions (fork exclusion, mode control, marker control, association control)
- fail CI immediately if a required boundary guard is removed

The purpose of this test is to guarantee the presence of the boundary policy. It is not an integration test of the full GitHub Actions runtime.

## 日本語

一次情報:
- `.github/workflows/agent-commands.yml`
- `.github/workflows/copilot-review-gate.yml`
- `.github/workflows/codex-autopilot-lane.yml`
- `.github/workflows/pr-ci-status-comment.yml`
- `.github/workflows/copilot-auto-fix.yml`

## 1. 権限境界マトリクス

| Workflow | Trigger | 境界条件 | 意図 |
| --- | --- | --- | --- |
| agent-commands (`copilot-review-gate dispatch`) | `issue_comment` | PRに紐づくコメントのみ、`github-actions[bot]` + `<!-- AE-COPILOT-AUTO-FIX v1 -->` を要求 | 任意コメントからのdispatch起動を防止 |
| Copilot Review Gate (`gate`) | `workflow_dispatch` | default branch 上の手動実行では `pr_number` が必要。未指定なら gate は skip または error になる | 無関係ブランチでの誤起動を防止 |
| Copilot Auto Fix | `pull_request_review` | fork PR除外、Copilot actor限定、global kill-switch考慮 | 書き込み権限と適用主体を制限 |
| Codex Autopilot Lane | `issue_comment` | PRコメント上の `/autopilot run`、権限者（MEMBER/OWNER/COLLABORATOR）、global kill-switch を要求 | 任意ユーザーコメントによる自動更新を防止 |
| Codex Autopilot Lane | `pull_request` | non-fork PR、`autopilot:on` label、global kill-switch を要求 | fork PR や unlabeled PR での autopilot 実行を防止 |
| Codex Autopilot Lane | `workflow_dispatch` | `pr_number` 入力と global kill-switch を要求 | operator が誤った PR を対象にすることを防止 |
| PR Maintenance (`update-branch`, `enable-auto-merge`) | `pull_request` / `workflow_dispatch` / `schedule` | fork PR除外（PR起点）、`workflow_dispatch` では `mode` の既定値が `both`、global kill-switch考慮 | 不要な更新/merge有効化を防止 |

## 2. 実装上の補足

- global kill-switch (`AE_AUTOMATION_GLOBAL_DISABLE`) は、更新系 / follow-up dispatch 系の lane（`Codex Autopilot Lane`, `PR Maintenance`, `Copilot Auto Fix`）で workflow 条件とスクリプト内部の両方からガードします。`Copilot Review Gate` 自体は現時点ではこの kill-switch の対象外です。
- `issue_comment` 起点は「PRに紐づいているか」を必須条件とし、必要な場合のみ actor/marker を追加検証します。
- `workflow_dispatch` 起点は `pr_number` や `mode` のような重要入力を必須化または既定化し、誤対象への実行を避けます。

## 3. テスト方針

最小限の境界回帰テストを `tests/unit/ci/workflow-permission-boundary.test.ts` で実施します。

- workflow定義内に必須ガード式（fork除外、mode制御、marker制御、association制御）が存在することを検証
- 境界ガード削除時にCIで即検知できるようにする

このテストは「仕様の存在保証」を目的とし、GitHub Actions実行環境そのものの統合テストは対象外です。
