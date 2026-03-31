---
docRole: ssot
lastVerified: '2026-03-31'
owner: agent-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Agent Documentation Boundary Matrix

> 🌍 Language / 言語: English | 日本語

---

## English

Last updated: 2026-03-31

Purpose: define the ownership boundary that keeps `AGENTS.md` and `docs/agents/*` from duplicating primary-source policy text.

### Boundary definitions (primary / secondary)

| Topic | Primary source (SSOT) | Secondary source (agent-facing route) | Managed scope |
| --- | --- | --- | --- |
| Overall CI policy | `docs/ci-policy.md` | `AGENTS.md`, `docs/agents/README.md` | required checks, opt-in controls, operating principles |
| CI operating procedure | `docs/ci/ci-operations-handbook.md` | `docs/agents/README.md` | daily monitoring, rerun, recovery procedure |
| CI incident recovery | `docs/ci/ci-troubleshooting-guide.md` | `AGENTS.md` decision table | failure classification and standard recovery flow |
| Claude Code entrypoint | `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`, `policy/risk-policy.yml` | `CLAUDE.md`, `AGENTS.md`, `docs/agents/README.md` | Claude Code routing, handoff entrypoint, risk policy routing |
| Risk / label evaluation | `policy/risk-policy.yml` | `AGENTS.md` invariants | `risk:low/high`, required labels, gate conditions |
| Slash command implementation | `.github/workflows/agent-commands.yml` | `AGENTS.md`, `docs/agents/README.md` | accepted commands, attached labels, dispatch implementation |
| Workflow permission boundary | `docs/ci/automation-permission-boundaries.md` | `AGENTS.md` progressive disclosure | boundary between `workflow_dispatch` and `issue_comment` |
| PR automation operations | `docs/ci/pr-automation.md` | `AGENTS.md` decision table | review gate, auto-fix, auto-merge operations |
| Multi-agent safety operations | `docs/agents/multi-agent-safety.md` | `AGENTS.md`, `docs/agents/README.md` | subagent permissions, ownership boundary, post-run checks |
| Dedicated worktree lifecycle | `docs/maintenance/subagent-worktree-runbook.md` | `docs/agents/multi-agent-safety.md` | worktree creation, isolation, integration, cleanup |

### Writing rules (drift prevention)
1. `AGENTS.md` stays router-only and does not retain detailed procedures or enumerations.
2. `CLAUDE.md` stays a Claude Code router and does not repeat detailed policy text.
3. `docs/agents/*` only carries routes to the primary source and does not duplicate the policy body.
4. when concrete values change, such as command names, labels, or required checks, update the primary-source document first and update secondary sources only as links or short routing notes.
5. for CI boundary detail, reference `docs/ci/ci-doc-boundary-matrix.md` and keep cross-links intact.
6. subagent safety detail belongs in `docs/agents/multi-agent-safety.md` and `docs/maintenance/subagent-worktree-runbook.md`; `AGENTS.md` should keep only invariants.

### Checks when changing these docs
- `pnpm -s run check:doc-consistency`
- `pnpm -s run check:ci-doc-index-consistency` when the affected route touches CI document indexes

## 日本語

最終更新: 2026-03-31

目的: `AGENTS.md` と `docs/agents/*` が一次情報を重複再掲しないための責務境界を定義する。

### 境界定義（一次情報 / 二次情報）

| テーマ | 一次情報（SSOT） | 二次情報（agent 向け導線） | 管理対象 |
| --- | --- | --- | --- |
| CI 全体方針 | `docs/ci-policy.md` | `AGENTS.md`, `docs/agents/README.md` | required checks / opt-in / 運用原則 |
| CI 運用手順 | `docs/ci/ci-operations-handbook.md` | `docs/agents/README.md` | 日次監視、再実行、復帰手順 |
| CI 障害復旧 | `docs/ci/ci-troubleshooting-guide.md` | `AGENTS.md` decision table | 失敗分類と標準復旧フロー |
| Claude Code 入口 | `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`, `policy/risk-policy.yml` | `CLAUDE.md`, `AGENTS.md`, `docs/agents/README.md` | Claude Code 向け導線、handoff 入口、risk policy 入口 |
| Risk / label 判定 | `policy/risk-policy.yml` | `AGENTS.md` invariants | `risk:low/high`、required labels、gate 条件 |
| slash command 実装 | `.github/workflows/agent-commands.yml` | `AGENTS.md`, `docs/agents/README.md` | 受理コマンド、付与ラベル、dispatch 実装 |
| workflow 権限境界 | `docs/ci/automation-permission-boundaries.md` | `AGENTS.md` progressive disclosure | `workflow_dispatch` / `issue_comment` の境界 |
| PR 自動化運用 | `docs/ci/pr-automation.md` | `AGENTS.md` decision table | review gate / auto-fix / auto-merge の運用 |
| multi-agent 安全運用 | `docs/agents/multi-agent-safety.md` | `AGENTS.md`, `docs/agents/README.md` | subagent 権限、担当境界、完了後確認 |
| 専用 worktree ライフサイクル | `docs/maintenance/subagent-worktree-runbook.md` | `docs/agents/multi-agent-safety.md` | worktree 作成、隔離、統合、回収 |

### 記述ルール（drift 防止）
1. `AGENTS.md` は router 専用とし、詳細手順や列挙を保持しない。
2. `CLAUDE.md` は Claude Code 専用 router とし、詳細説明や policy 本文を再掲しない。
3. `docs/agents/*` は一次情報への導線のみを持ち、policy 本文を複製しない。
4. コマンド名、ラベル名、required checks のような実装値が変わった場合は、一次情報ファイルを先に更新し、二次情報は link または短い routing note だけを更新する。
5. CI 境界の詳細は `docs/ci/ci-doc-boundary-matrix.md` を参照し、相互 link を維持する。
6. subagent 安全運用の詳細は `docs/agents/multi-agent-safety.md` と `docs/maintenance/subagent-worktree-runbook.md` に集約し、`AGENTS.md` には invariants のみ記載する。

### 変更時チェック
- `pnpm -s run check:doc-consistency`
- 影響範囲が CI document index に及ぶ場合は `pnpm -s run check:ci-doc-index-consistency`
