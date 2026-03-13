---
docRole: ssot
canonicalSource: docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-READINESS.md
lastVerified: '2026-03-13'
owner: project-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Apache License Cutover Approval Readiness

## Purpose

`apache-license-cutover-approval-readiness-audit/v1` validates that the human approval record is complete, SHA-consistent, and aligned with `apache-license-cutover-readiness-audit/v1`.

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

## What it checks

1. The approval record contains a valid `head SHA`.
2. The approval record `head SHA`, the cutover readiness audit `gitHeadSha`, and the current repository `HEAD` match.
3. All required audit artifact paths are filled in.
4. The approval table has no unsupported decision values.
5. The decision block is consistent with the table rows.
6. `approved for cutover: yes` is only allowed when all required approval rows are approved and the cutover readiness audit is `ready`.

## Status meanings

- `blocked`
  - the approval record is incomplete, contradictory, or SHA-mismatched
- `human-review-required`
  - the record is structurally valid, but approvals are still pending
- `ready`
  - the record is complete and internally consistent, and the cutover PR can be opened from an approval-record perspective

## Related documents

- `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md`
- `docs/project/APACHE-LICENSE-CUTOVER-READINESS.md`
- `docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md`
