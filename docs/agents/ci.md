# Agents Runbook: CI

## When to use

- PRでrequired checkが失敗したとき
- 失敗原因の一次切り分けと再実行が必要なとき

## What to load (primary sources)

- `docs/ci-policy.md`
- `docs/ci/ci-operations-handbook.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `.github/workflows/*.yml`

## Commands (copy/paste)

```bash
gh pr checks <PR_NUMBER> --required
```

```bash
gh run view <RUN_ID> --log-failed
```

```bash
gh run rerun <RUN_ID>
```

```bash
pnpm -s run check:doc-consistency
```

## Artifacts to check

- `artifacts/ci/*`
- PRの「CI Status Snapshot」コメント
- 失敗ジョブのStep Summary

## Escalation / follow-up

- required checkが仕様通りにfailしている場合は、PRに「再現コマンド・原因・修正方針」を記載
- fail-open/fail-closed判断が必要な場合は `docs/ci/automation-failure-policies.md` に沿って判断
