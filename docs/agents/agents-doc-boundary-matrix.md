# Agent Documentation Boundary Matrix

最終更新: 2026-02-26

目的: `AGENTS.md` と `docs/agents/*` が一次情報を重複再掲しないための責務境界を定義する。

## 境界定義（一次情報 / 二次情報）

| テーマ | 一次情報（SSOT） | 二次情報（Agent向け導線） | 管理対象 |
| --- | --- | --- | --- |
| CI全体方針 | `docs/ci-policy.md` | `AGENTS.md`, `docs/agents/README.md` | Required checks / opt-in / 運用原則 |
| CI運用手順 | `docs/ci/ci-operations-handbook.md` | `docs/agents/README.md` | 日次監視、再実行、復帰手順 |
| CI障害復旧 | `docs/ci/ci-troubleshooting-guide.md` | `AGENTS.md` Decision Table | 失敗分類、復旧の標準手順 |
| Risk/Label判定 | `policy/risk-policy.yml` | `AGENTS.md` Invariants | `risk:low/high`、required labels、gate条件 |
| Slash Commands 実装 | `.github/workflows/agent-commands.yml` | `AGENTS.md`, `docs/agents/README.md` | 受理コマンド、付与ラベル、dispatch実装 |
| Workflow権限境界 | `docs/ci/automation-permission-boundaries.md` | `AGENTS.md` Progressive Disclosure | `workflow_dispatch` / `issue_comment` の境界 |
| PR自動化運用 | `docs/ci/pr-automation.md` | `AGENTS.md` Decision Table | review gate / auto-fix / auto-merge の運用 |

## 記述ルール（ドリフト防止）

1. `AGENTS.md` はルータ専用とし、詳細手順・列挙は保持しない。  
2. `docs/agents/*` は一次情報への導線のみを持ち、ポリシー本文を複製しない。  
3. 実装値（コマンド名、ラベル名、required checks）は一次情報ファイルを更新し、二次情報はリンクのみ更新する。  
4. CI境界の詳細は `docs/ci/ci-doc-boundary-matrix.md` を参照し、相互リンクを維持する。  

## 変更時チェック

- `pnpm -s run check:doc-consistency`
- 必要に応じて `pnpm -s run check:ci-doc-index-consistency`

