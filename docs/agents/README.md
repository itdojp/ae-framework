# Agent Docs Index

`AGENTS.md` から参照する、エージェント向けの索引です。  
ここでは一次情報の場所のみを示し、方針本文の重複を避けます。

## ドメイン別 runbook

- CI: `docs/agents/ci.md`
- PR: `docs/agents/pr.md`
- Spec: `docs/agents/spec.md`
- Formal Methods: `docs/agents/formal.md`
- Context Pack: `docs/agents/context-pack.md`
- Security: `docs/agents/security.md`

## 主要ドメインと一次情報

- 境界定義（一次/二次）: `docs/agents/agents-doc-boundary-matrix.md`
- CI方針（SSOT）: `docs/ci-policy.md`
- CI運用: `docs/ci/ci-operations-handbook.md`
- CI障害復旧: `docs/ci/ci-troubleshooting-guide.md`
- PR自動化運用: `docs/ci/pr-automation.md`
- Prompt Pack（検証プロンプト集）: `docs/agents/recipes/README.md`
- 権限境界: `docs/ci/automation-permission-boundaries.md`
- Risk/Label判定: `policy/risk-policy.yml`
- Slash Commands実装: `.github/workflows/agent-commands.yml`
- Workflow責務整理: `docs/ci/workflow-role-matrix.md`

## 利用順

1. `AGENTS.md` の Decision Table で作業タイプを決める
2. この索引から一次情報とrunbookを開く
3. 実行結果を PR コメントと artifacts に残す

## 関連Issue

- #2292: ドメイン別runbook（`docs/agents/ci.md`, `pr.md`, `spec.md`, `formal.md`, `context-pack.md`, `security.md`）
- #2293: Agent文書の境界表（一次情報/二次情報）
- #2294: Slash Commands / Labels の docs 同期自動化
