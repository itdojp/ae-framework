---
docRole: derived
canonicalSource:
- docs/ci/pr-automation.md
- policy/risk-policy.yml
lastVerified: '2026-03-31'
---

# Agents Runbook: Pull Request

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need to prepare the minimum PR body and evidence set before requesting review
- when you need to decide whether to apply or reject review feedback and record the rationale

### What to load (primary sources)
- `.github/pull_request_template.md`
- `docs/ci/pr-automation.md`
- `docs/ci-policy.md`
- `policy/risk-policy.yml`

### Commands (copy/paste)
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

### Artifacts to check
- the PR body, especially Rollback, Acceptance, and validation steps
- top-level review comments, inline replies, and thread resolution status
- the latest `policy-gate`, `gate`, and `verify-lite` results

### Escalation / follow-up
- if you intentionally do not apply a review suggestion, leave the reason in the PR thread or an explicit PR comment
- if `risk:high` requires extra human approvals, record the policy block and wait instead of overriding it
- if required checks are blocked by unresolved AI review threads, resolve the threads first and then rerun or refresh the head branch

## 日本語

### When to use
- review 依頼前に、PR 本文と evidence の最小セットを整えたいとき
- review 指摘を採用するか見送るかを判断し、根拠を残したいとき

### What to load (primary sources)
- `.github/pull_request_template.md`
- `docs/ci/pr-automation.md`
- `docs/ci-policy.md`
- `policy/risk-policy.yml`

### Commands (copy/paste)
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

### Artifacts to check
- PR 本文、特に Rollback、Acceptance、検証手順
- review 本文、インライン返信、thread の解消状態
- 最新の `policy-gate`、`gate`、`verify-lite` 結果

### Escalation / follow-up
- review suggestion を意図的に採用しない場合は、その理由を thread または明示的な PR comment に残す
- `risk:high` で追加の human approval が必要な場合は、override せずに policy block として記録して待機する
- unresolved な AI review thread が原因で required checks が block している場合は、先に thread を解消してから rerun、または head branch 更新を行う
