# Agents Runbook: Pull Request

## When to use

- PR作成時に記載内容を最小セットで整えたいとき
- レビュー対応で「修正する/しない」の判断根拠を残すとき

## What to load (primary sources)

- `.github/pull_request_template.md`
- `docs/ci/pr-automation.md`
- `policy/risk-policy.yml`

## Commands (copy/paste)

```bash
gh pr view "$PR_NUMBER" --json title,body,labels,reviewDecision,statusCheckRollup
```

```bash
gh api "repos/itdojp/ae-framework/pulls/${PR_NUMBER}/comments" --paginate
```

```bash
gh api "repos/itdojp/ae-framework/pulls/${PR_NUMBER}/reviews" --paginate
```

```bash
gh pr checks "$PR_NUMBER" --required
```

## Artifacts to check

- PR本文（Rollback / Acceptance / 検証手順）
- レビュー本文・インライン返信・解決状態
- `policy-gate` と `verify-lite` の最新結果

## Escalation / follow-up

- 非採用コメントがある場合は、理由をPRコメントで明示
- `risk:high` でApprove不足の場合は、仕様上のブロックとして記録して待機
