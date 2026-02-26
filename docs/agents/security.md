# Agents Runbook: Security

## When to use

- セキュリティ系ジョブ（scan/audit/secrets）の失敗対応
- 依存更新時の最低限の安全確認

## What to load (primary sources)

- `SECURITY.md`
- `docs/ci/automation-permission-boundaries.md`
- `docs/ci/OPT-IN-CONTROLS.md`

## Commands (copy/paste)

```bash
pnpm -s run verify:security
```

```bash
pnpm -s run security:scan
```

```bash
pnpm -s run security:audit
```

```bash
pnpm -s run security:secrets
```

## Artifacts to check

- `artifacts/security/*`
- `artifacts/sbom/*`
- Security系workflowのStep Summary

## Escalation / follow-up

- 誤検知の可能性がある場合も、除外根拠をPRに明示する
- 高リスク変更では `run-security` ラベル運用と `policy-gate` 判定結果を合わせて記録する
