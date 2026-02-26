# AGENTS — ae-framework Router

このファイルは、エージェント作業時の最小ルータです。  
詳細手順はドメイン別ドキュメントを参照し、本ファイルへの重複列挙を避けます。

## Decision Table

| 依頼タイプ | 最初に読む一次情報 | 実行前の判断ポイント | 結果確認先 |
| --- | --- | --- | --- |
| CI失敗の復旧 | `docs/ci/ci-troubleshooting-guide.md` | required check か opt-in か | 対象Jobログ / PRコメント |
| PR自動化・レビュー運用 | `docs/ci/pr-automation.md` | auto-fix / auto-merge の有効条件 | `gate` / `policy-gate` / automationコメント |
| Risk判定・ラベル運用 | `policy/risk-policy.yml` | `risk:low` / `risk:high` と required labels | `policy-gate` サマリ |
| GitHub Actions修正 | `.github/workflows/*.yml` | `printf`運用・権限境界・再現性 | `actionlint` / 対象workflow結果 |
| Slash Command運用 | `.github/workflows/agent-commands.yml` | 受理コマンド・付与ラベルの実装値 | PRコメント / 付与ラベル |
| 形式手法・仕様検証 | `docs/quality/formal-runbook.md` | 実行対象（TLA+/CSP/Lean/Alloy等）と証跡 | `artifacts/formal/*` |

## Invariants（不変条件）

- Required checks の基準は `verify-lite` + `policy-gate`（branch protection 設定を一次情報とする）。
- Riskラベルと判定規則の一次情報は `policy/risk-policy.yml`。  
  `risk:high` は最小1名の人間Approve、必要に応じて policy label / 追加ゲートを要求する。
- GitHub Actions の出力書き込みは `printf` を使用し、`$GITHUB_OUTPUT` / `$GITHUB_ENV` への追記はシェル安全性を維持する。
- 方針は `docs/ci-policy.md`、運用は `docs/ci/*` を一次情報として参照し、AGENTSに再掲しない。

## Progressive Disclosure（参照順）

1. `docs/agents/README.md`（エージェント向け索引）
2. `docs/agents/agents-doc-boundary-matrix.md`（一次情報/二次情報の境界定義）
3. `docs/agents/handoff.md`（AE-HANDOFFの標準プロトコル）
4. `docs/agents/recipes/README.md`（検証プロンプト集 / Prompt Pack）
5. `docs/ci-policy.md`（CI方針のSSOT）
6. `docs/ci/ci-operations-handbook.md`（日次運用）
7. `docs/ci/ci-troubleshooting-guide.md`（失敗時の復旧手順）
8. `docs/ci/pr-automation.md`（Copilotレビュー後の自動化フロー）
9. `docs/ci/automation-permission-boundaries.md`（workflow_dispatch / issue_comment 権限境界）
10. `.github/workflows/agent-commands.yml`（Slash Commands 実装値）
11. `policy/risk-policy.yml`（risk/label 判定のSSOT）

## Scope

- このファイルは「入口（Router）」のみを保持する。
- 実行コマンド詳細、Slash Command一覧、ラベル詳細条件は一次情報へリンクし、ここでは列挙しない。
- ドメイン別runbook追加は `docs/agents/*` で段階的に拡張する（関連: #2292）。
