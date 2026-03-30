---
docRole: derived
canonicalSource:
- docs/agents/agents-doc-boundary-matrix.md
lastVerified: '2026-03-31'
---

# Agent Docs Index

> 🌍 Language / 言語: English | 日本語

---

## English

This is the agent-facing index referenced from `AGENTS.md`. It points only to the primary documents and avoids duplicating policy text.

### Root routers
- `AGENTS.md`: minimal router shared by all agents
- `CLAUDE.md`: minimal router for Claude Code

### Domain runbooks
- CI: `docs/agents/ci.md`
- PR: `docs/agents/pr.md`
- Spec: `docs/agents/spec.md`
- Formal Methods: `docs/agents/formal.md`
- Context Pack: `docs/agents/context-pack.md`
- Security: `docs/agents/security.md`
- Multi-agent Safety: `docs/agents/multi-agent-safety.md`

### Primary domains and primary sources
- boundary definitions (primary / secondary): `docs/agents/agents-doc-boundary-matrix.md`
- CI policy (SSOT): `docs/ci-policy.md`
- CI operations: `docs/ci/ci-operations-handbook.md`
- CI incident recovery: `docs/ci/ci-troubleshooting-guide.md`
- PR automation operations: `docs/ci/pr-automation.md`
- Codex Autopilot Lane: `docs/ci/codex-autopilot-lane.md`
- automation reason codes: `docs/ci/reason-codes.md`
- Prompt Pack (verification prompts): `docs/agents/recipes/README.md`
- Continuous Loop contract: `docs/agents/recipes/continuous-loop.md`
- handoff standard protocol / builder / validator: `docs/agents/handoff.md`
- hook feedback adapter: `docs/agents/hook-feedback.md`
- permission boundary: `docs/ci/automation-permission-boundaries.md`
- risk / label policy: `policy/risk-policy.yml`
- slash command implementation: `.github/workflows/agent-commands.yml`
- slash command catalog (generated): `docs/agents/commands.md`
- workflow role mapping: `docs/ci/workflow-role-matrix.md`
- subagent dedicated worktree operations: `docs/maintenance/subagent-worktree-runbook.md`

### Recommended usage order
1. use the decision table in `AGENTS.md` to determine the work type
2. if subagents are involved, read `docs/agents/multi-agent-safety.md` and `docs/maintenance/subagent-worktree-runbook.md` first
3. open the relevant primary source or runbook from this index
4. leave execution results in PR comments and artifacts

### Related issues
- `#2292`: domain runbooks (`docs/agents/ci.md`, `pr.md`, `spec.md`, `formal.md`, `context-pack.md`, `security.md`)
- `#2293`: agent documentation boundary matrix (primary / secondary)
- `#2294`: automated sync for slash command and label documentation

## 日本語

`AGENTS.md` から参照する、エージェント向けの索引です。ここでは一次情報の場所のみを示し、方針本文の重複を避けます。

### Root routers
- `AGENTS.md`: 全エージェント共通の最小ルータ
- `CLAUDE.md`: Claude Code 向けの最小ルータ

### ドメイン別 runbook
- CI: `docs/agents/ci.md`
- PR: `docs/agents/pr.md`
- Spec: `docs/agents/spec.md`
- Formal Methods: `docs/agents/formal.md`
- Context Pack: `docs/agents/context-pack.md`
- Security: `docs/agents/security.md`
- Multi-agent Safety: `docs/agents/multi-agent-safety.md`

### 主要ドメインと一次情報
- 境界定義（一次 / 二次）: `docs/agents/agents-doc-boundary-matrix.md`
- CI 方針（SSOT）: `docs/ci-policy.md`
- CI 運用: `docs/ci/ci-operations-handbook.md`
- CI 障害復旧: `docs/ci/ci-troubleshooting-guide.md`
- PR 自動化運用: `docs/ci/pr-automation.md`
- Codex Autopilot Lane: `docs/ci/codex-autopilot-lane.md`
- automation reason codes: `docs/ci/reason-codes.md`
- Prompt Pack（検証プロンプト集）: `docs/agents/recipes/README.md`
- Continuous Loop contract: `docs/agents/recipes/continuous-loop.md`
- handoff 標準プロトコル / builder / validator: `docs/agents/handoff.md`
- hook feedback adapter: `docs/agents/hook-feedback.md`
- 権限境界: `docs/ci/automation-permission-boundaries.md`
- Risk / label policy: `policy/risk-policy.yml`
- slash command 実装: `.github/workflows/agent-commands.yml`
- slash command catalog（生成）: `docs/agents/commands.md`
- workflow role mapping: `docs/ci/workflow-role-matrix.md`
- subagent 専用 worktree 運用: `docs/maintenance/subagent-worktree-runbook.md`

### 利用順
1. `AGENTS.md` の decision table で作業タイプを決める
2. subagent を使う場合は `docs/agents/multi-agent-safety.md` と `docs/maintenance/subagent-worktree-runbook.md` を先に確認する
3. この索引から一次情報と runbook を開く
4. 実行結果を PR comment と artifacts に残す

### 関連 Issue
- `#2292`: ドメイン別 runbook（`docs/agents/ci.md`, `pr.md`, `spec.md`, `formal.md`, `context-pack.md`, `security.md`）
- `#2293`: agent 文書の境界表（一次情報 / 二次情報）
- `#2294`: slash command / label の docs 同期自動化
