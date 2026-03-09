# CLAUDE — ae-framework Router

Claude Code 利用時の最小入口です。  
詳細手順やポリシー本文は一次情報へ委譲し、このファイルに再掲しません。

## Read Order

1. `AGENTS.md` — 全エージェント共通の最小ルータ
2. `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md` — Claude Code 向け統合ガイド
3. `docs/agents/README.md` — agent 向け索引
4. `docs/agents/handoff.md` — AE-HANDOFF プロトコル
5. `policy/risk-policy.yml` — risk / label / required gate の SSOT

## Role Boundary

- `AGENTS.md`: 全エージェント共通の入口
- `CLAUDE.md`: Claude Code 固有の入口
- 詳細な運用・実装値・コマンド列挙は一次情報へ委譲

## Invariants

- `risk:high` の条件と required labels は `policy/risk-policy.yml` を優先する
- handoff は `docs/agents/handoff.md` の AE-HANDOFF に従う
- multi-agent / subagent の安全運用は `AGENTS.md` と `docs/agents/multi-agent-safety.md` を優先する
- commit / push / PR / Issue 更新前には対象 workflow / policy / docs の一次情報を確認する

## Scope

- このファイルは Claude Code の「入口」だけを定義する
- Claude Code 向けの長文説明、実装詳細、サンプルフローは `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md` を参照する
