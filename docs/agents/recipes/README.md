---
docRole: ssot
lastVerified: '2026-04-01'
owner: agent-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Agent Prompt Pack (Recipes)

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
`docs/agents/recipes/*` contains short operator recipes for recurring validation and recovery tasks. Use this index when you need the smallest actionable command set before loading the longer runbooks.

### Recipes
- Verify Lite: `docs/agents/recipes/verify-lite.md`
- Spec / IR / Drift: `docs/agents/recipes/spec-ir-drift.md`
- Quality Profile: `docs/agents/recipes/quality-profile.md`
- Formal Quickstart: `docs/agents/recipes/formal-quickstart.md`
- Continuous Loop Contract (CodeX): `docs/agents/recipes/continuous-loop.md`

### Operating rules
- every recipe must link to its primary sources such as policy, workflow, or runbook documents
- commands should stay limited to the minimum copy/paste set needed to reproduce the target check
- every recipe should state the immediate next action to take when the check fails

## 日本語

### 概要
`docs/agents/recipes/*` は、頻出の検証・復旧作業を短い手順で再現するための operator recipe 集です。長い runbook を開く前に、最小の実行コマンドを確認したい場合はこの index を起点にします。

### Recipes
- Verify Lite: `docs/agents/recipes/verify-lite.md`
- Spec / IR / Drift: `docs/agents/recipes/spec-ir-drift.md`
- Quality Profile: `docs/agents/recipes/quality-profile.md`
- Formal Quickstart: `docs/agents/recipes/formal-quickstart.md`
- Continuous Loop Contract (CodeX): `docs/agents/recipes/continuous-loop.md`

### 運用ルール
- 各 recipe は、policy / workflow / runbook などの一次情報へのリンクを必ず持つ
- command は、対象チェックを再現するために必要な最小の copy/paste set に限定する
- failure 時に次に取るべき action を必ず記載する
