---
docRole: derived
canonicalSource:
- docs/ci-policy.md
- docs/ci/ci-operations-handbook.md
- docs/ci/ci-troubleshooting-guide.md
lastVerified: '2026-03-31'
---

# Agents Runbook: CI

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when a PR required check has failed
- when you need an initial triage and rerun plan for CI failures

### What to load (primary sources)
- `docs/ci-policy.md`
- `docs/ci/ci-operations-handbook.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-failure-policies.md`
- `.github/workflows/*.yml`

### Commands (copy/paste)
```bash
gh pr checks "$PR_NUMBER" --required
```

```bash
gh run view "$RUN_ID" --log-failed
```

```bash
gh run rerun "$RUN_ID"
```

```bash
pnpm -s run check:doc-consistency
```

### Artifacts to check
- `artifacts/ci/*`
- the PR `CI Status Snapshot` comment
- step summaries from failed jobs

### Escalation / follow-up
- if a required check is failing by design, leave the repro command, cause, and fix plan in the PR comment
- if you need a fail-open / fail-closed judgment, follow `docs/ci/automation-failure-policies.md`
- if the check is blocked by unresolved AI review threads, resolve the threads first and then rerun or refresh the head branch

## 日本語

### When to use
- PR で required check が失敗したとき
- 失敗原因の一次切り分けと再実行方針が必要なとき

### What to load (primary sources)
- `docs/ci-policy.md`
- `docs/ci/ci-operations-handbook.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-failure-policies.md`
- `.github/workflows/*.yml`

### Commands (copy/paste)
```bash
gh pr checks "$PR_NUMBER" --required
```

```bash
gh run view "$RUN_ID" --log-failed
```

```bash
gh run rerun "$RUN_ID"
```

```bash
pnpm -s run check:doc-consistency
```

### Artifacts to check
- `artifacts/ci/*`
- PR の `CI Status Snapshot` comment
- 失敗 job の step summary

### Escalation / follow-up
- required check が仕様どおりに fail している場合は、PR に repro command、原因、修正方針を記載する
- fail-open / fail-closed 判断が必要な場合は `docs/ci/automation-failure-policies.md` に従う
- unresolved な AI review thread が原因で block している場合は、先に thread を解消してから rerun、または head branch 更新を行う
