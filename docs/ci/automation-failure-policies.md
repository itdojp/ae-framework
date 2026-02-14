# Automation Failure Policies and Comment Templates

PR 自動化ワークフローの fail-open / fail-closed 方針と、運用で参照するコメントテンプレートを定義します。

## 1. 判定方針（fail-open / fail-closed）

- `fail-closed`: 判定に不確実性がある場合は自動更新/自動マージを実行しない
- `fail-open`: 失敗時も保守的に処理をスキップし、PR本体の進行を不必要に止めない

| Workflow / Job | 主目的 | 方針 | 根拠（一次情報） |
| --- | --- | --- | --- |
| `Copilot Review Gate / gate` | Copilot レビュー必須化 | fail-closed | review不在/未解決threadで `gate` を failure にする（`.github/workflows/copilot-review-gate.yml`） |
| `Copilot Auto Fix / auto-fix` | suggestion 自動適用 | fail-closed | actor/scope/head整合が崩れる場合は `skip` で停止し書き換えしない（`scripts/ci/copilot-auto-fix.mjs`） |
| `PR Maintenance / enable-auto-merge` | auto-merge 有効化 | fail-closed | required checks/review/保護情報が不十分な場合は `blocked` で停止（`scripts/ci/auto-merge-enabler.mjs`） |
| `PR Maintenance / update-branch` | behind 解消 | 条件別（conflict は fail-open / その他は fail-closed） | conflict はコメントを残して停止、非conflictエラーは `core.setFailed(...)` で job を失敗終了（`.github/workflows/pr-ci-status-comment.yml`） |
| `PR Self-Heal / self-heal` | failed/behind の復旧 | fail-closed | 復旧不能時は `status:blocked` を付与し明示停止（`scripts/ci/pr-self-heal.mjs`） |
| `Codex Autopilot Lane / autopilot` | touchless merge lane | fail-closed | conflict/gate不一致/未収束時は `status:blocked` で停止（`scripts/ci/codex-autopilot-lane.mjs`） |
| `PR Maintenance / post-status` | 状態可視化 | fail-open | 情報投稿専用。失敗してもマージ条件判定はこのjobに依存しない（`scripts/ci/pr-ci-status-comment.mjs`） |

## 2. コメントテンプレート（marker付き）

運用で「どの自動化が何を判断したか」を即時に識別するため、以下の marker を先頭に付けます。

### 2.1 Copilot Auto Fix

```md
<!-- AE-COPILOT-AUTO-FIX v1 -->
## Copilot Auto Fix (<ISO8601>)
- PR: #<number>
- actor: <actor>
- scope: <docs|all>
- applied: <n> (already: <n>)
- resolved threads: <n>
- changed files: <csv>
- skipped: <n>
- note: <reason>
```

### 2.2 Auto Merge Status

```md
<!-- AE-AUTO-MERGE-STATUS v1 -->
## Auto-merge Status (<ISO8601>)
- #<number> <title>
- mergeable: <MERGEABLE|...>
- review: <APPROVED|...> (required: <yes/no>)
- checks: ✅<n> ❌<n> ⏳<n>
- failed checks: <csv>
- reason: <reason>
- auto-merge: already enabled
```

### 2.3 PR Self-Heal

```md
<!-- AE-SELF-HEAL v1 -->
## PR Self-Heal (<ISO8601>)
- PR: #<number> <title>
- status: <resolved|blocked|skip|error>
- rounds: <n>
- dry-run: <true|false>
- mergeable: <value>
- merge state: <value>
- checks: success=<n>, failure=<n>, pending=<n>
- reason: <reason>
- actions:
  - round<n>: <action>
```

### 2.4 Codex Autopilot Lane

```md
<!-- AE-CODEX-AUTOPILOT v1 -->
## Codex Autopilot Lane (<ISO8601>)
- PR: #<number> <title>
- status: <done|blocked|skip|error>
- rounds: <n>
- dry-run: <true|false>
- gate: <success|failure|pending|missing>
- unresolved copilot threads: <n>
- mergeable: <value>
- merge state: <value>
- reason: <reason>
- actions:
  - round<n>: <action>
```

### 2.5 CI Status Snapshot

```md
<!-- AE-CI-STATUS v1 -->
## CI Status Snapshot (<ISO8601>)
- #<number> <title> | ✅<n> ❌<n> ⏳<n> ⏭️<n> | review:<state> | mergeable:<state>
  - failed: <csv>
```

### 2.6 Auto Update Branch

```md
<!-- AE-PR-AUTO-UPDATE -->

### Auto Update Branch
PR #<number> was behind base; triggered branch update.
If conflicts remain, manual resolution is required.
```

競合時:

```md
<!-- AE-PR-AUTO-UPDATE -->

### Auto Update Branch
PR #<number> could not be auto-updated due to conflicts.
Details: <error>
Please resolve conflicts manually.
```

## 3. 運用ルール（最小）

- marker 付きコメントを削除せず update する（履歴の連続性を維持）
- `status:blocked` は「自動復旧不能」の明示として扱う
- fail-closed 系の job は rerun 前に reason 行を確認し、条件不足か実装不具合かを切り分ける
