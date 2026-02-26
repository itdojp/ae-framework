# Agent Docs Index

`AGENTS.md` から参照する、エージェント向けの索引です。  
ここでは一次情報の場所のみを示し、方針本文の重複を避けます。

## 主要ドメインと一次情報

- CI方針（SSOT）: `docs/ci-policy.md`
- CI運用: `docs/ci/ci-operations-handbook.md`
- CI障害復旧: `docs/ci/ci-troubleshooting-guide.md`
- PR自動化運用: `docs/ci/pr-automation.md`
- 権限境界: `docs/ci/automation-permission-boundaries.md`
- Risk/Label判定: `policy/risk-policy.yml`
- Slash Commands実装: `.github/workflows/agent-commands.yml`
- Slash Commands catalog（生成）: `docs/agents/commands.md`
- Workflow責務整理: `docs/ci/workflow-role-matrix.md`

## 利用順

1. `AGENTS.md` の Decision Table で作業タイプを決める
2. この索引から一次情報を開く
3. 実行結果を PR コメントと artifacts に残す

## 今後の拡張

- ドメイン別runbook（`docs/agents/ci.md`, `pr.md`, `spec.md`, `formal.md`, `context-pack.md`, `security.md`）は #2292 で追加する。
- Agent文書の境界表（一次情報/二次情報）は #2293 で定義する。
