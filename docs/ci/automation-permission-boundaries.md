# Automation Permission Boundaries

PR自動化ワークフローにおける `workflow_dispatch` / `issue_comment` 起点の権限境界を整理します。

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
| Copilot Review Gate (`gate`) | `workflow_dispatch` | `pr_number` 必須（main以外で手動実行時） | 無関係ブランチでの誤起動を防止 |
| Copilot Auto Fix | `pull_request_review` | fork PR除外、Copilot actor限定、global kill-switch考慮 | 書き込み権限と適用主体を制限 |
| Codex Autopilot Lane | `issue_comment` / `pull_request` / `workflow_dispatch` | `/autopilot run` + 権限者（MEMBER/OWNER/COLLABORATOR）+ PRコメント限定、global kill-switch考慮 | 任意ユーザーコメントによる自動更新を防止 |
| PR Maintenance (`update-branch`, `enable-auto-merge`) | `pull_request` / `workflow_dispatch` / `schedule` | fork PR除外（PR起点）、`mode` 明示、global kill-switch考慮 | 不要な更新/merge有効化を防止 |

## 2. 実装上の補足

- global kill-switch (`AE_AUTOMATION_GLOBAL_DISABLE`) は workflow 条件とスクリプト内部の両方でガードします。
- `issue_comment` 起点は「PRに紐づいているか」を必須条件とし、必要な場合のみ actor/marker を追加検証します。
- `workflow_dispatch` 起点は入力（`pr_number`, `mode`）を必須化し、誤対象への実行を避けます。

## 3. テスト方針

最小限の境界回帰テストを `tests/unit/ci/workflow-permission-boundary.test.ts` で実施します。

- workflow定義内に必須ガード式（fork除外、mode制御、marker制御、association制御）が存在することを検証
- 境界ガード削除時にCIで即検知できるようにする

このテストは「仕様の存在保証」を目的とし、GitHub Actions実行環境そのものの統合テストは対象外です。
