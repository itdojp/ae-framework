# CI Documentation Boundary Matrix

最終更新: 2026-02-26

目的: `docs/ci` 配下の運用ドキュメントについて、重複を抑えた責務境界を定義する。

Agent文書側の境界定義は `docs/agents/agents-doc-boundary-matrix.md` を参照。

## 境界定義（主文書と個別runbook）

| 区分 | 正式な主文書 | 補助runbook / 関連資料 | 管理対象 |
| --- | --- | --- | --- |
| 全体方針 | `docs/ci-policy.md` | `docs/ci/workflow-role-matrix.md`, `docs/ci/OPT-IN-CONTROLS.md` | Required checks / opt-in labels / dispatch方針 |
| 日次運用 | `docs/ci/ci-operations-handbook.md` | `docs/ci/ci-troubleshooting-guide.md` | 監視・再実行・停止/復帰の標準手順 |
| PR自動化 | `docs/ci/pr-automation.md` | `docs/ci/copilot-review-gate.md`, `docs/ci/copilot-auto-fix.md`, `docs/ci/auto-merge.md` | Copilot review gate / auto-fix / auto-merge |
| Docs検証 | `docs/ci/docs-doctest-policy.md` | `scripts/ci/check-docs-doctest-policy-sync.mjs` | docs-doctest 実行境界と同期チェック |
| 障害対応 | `docs/ci/automation-failure-policies.md` | `docs/ci/automation-rollback-runbook.md`, `docs/ci/automation-alerting.md` | fail-open/fail-closed, rollback, 通知 |

## 重複削減ルール

1. 方針は `docs/ci-policy.md` に集約し、実行手順は `docs/ci/ci-operations-handbook.md` へ集約する。  
2. `docs/ci-policy.md` には詳細トラブルシュートを再掲せず、該当runbookへのリンクを置く。  
3. `docs/README.md` と `docs/ci-policy.md` のCI導線は、同一の必須リンク集合を維持する。  
4. CI導線の整合は `pnpm run check:ci-doc-index-consistency` で機械検証する。
