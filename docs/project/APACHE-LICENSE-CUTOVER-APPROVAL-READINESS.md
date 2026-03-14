---
docRole: ssot
canonicalSource: docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-READINESS.md
lastVerified: '2026-03-14'
owner: project-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Apache License Cutover Approval Readiness

## Purpose

`apache-license-cutover-approval-readiness-audit/v1` validates that the human approval record is complete, aligned with `apache-license-cutover-readiness-audit/v1`, and only drifts from the reviewed approval snapshot in cutover-allowed paths.

This audit does not make the legal decision. It verifies that the decision record is internally consistent before opening the actual cutover PR.

## Inputs

- `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md`
- `artifacts/reference/legal/apache-license-cutover-readiness-audit.json`

## Command

```bash
pnpm run license:audit:approval -- \
  --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md \
  --cutover-readiness-audit artifacts/reference/legal/apache-license-cutover-readiness-audit.json \
  --output-json artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.json \
  --output-md artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.md
```

For the final pre-cutover run, prefer the wrapper command below so the factual audits and approval audit are regenerated from the same HEAD in one step.

```bash
SOURCE_DATE_EPOCH=<unix-seconds> pnpm run license:audit:precutover -- \
  --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md
```

## What it checks

1. The approval record contains a valid `head SHA`.
2. The cutover readiness audit `gitHeadSha` and the current repository `HEAD` match.
3. If the approval record `head SHA` differs from the current `HEAD`, the changed files between them are limited to cutover-allowed paths (`LICENSE`, `NOTICE`, `package.json`, outward-facing legal docs, `docs/project/**`, `artifacts/reference/legal/**`) and the approval-readiness infrastructure files that support the cutover gate itself.
4. All required audit artifact paths are filled in.
5. The approval table has no unsupported decision values.
6. The decision block is consistent with the table rows.
7. `approved for cutover: yes` is only allowed when all required approval rows are approved and the cutover readiness audit is not `blocked`.

## Status meanings

- `blocked`
  - the approval record is incomplete, contradictory, differs from the current cutover HEAD outside the allowed cutover scope, or the cutover readiness audit still has factual blockers
- `human-review-required`
  - the record is structurally valid, but approvals are still pending
- `ready`
  - the record is complete and internally consistent, and the cutover PR can be opened from an approval-record perspective even if the upstream cutover readiness audit remains `human-review-required`

## Related documents

- `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md`
- `docs/project/APACHE-LICENSE-CUTOVER-READINESS.md`
- `docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md`
