---
docRole: ssot
canonicalSource: docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md
lastVerified: '2026-03-13'
owner: project-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Apache License Cutover Approval Record

## Purpose

This document records the human approvals required before opening the actual Apache-2.0 cutover PR tracked by `#2623`.

It is not a legal opinion. It is the operator-facing record that links factual audits to explicit approval outcomes.

## Scope

Use this record only for the final cutover decision that changes:

- root `LICENSE`
- root `NOTICE`
- root `package.json` `license`
- outward-facing license wording in `README.md` and `CONTRIBUTING.md`

## Audit Baseline

Record the exact commit and audit artifacts reviewed for the decision.

- head SHA:
- `artifacts/reference/legal/license-scope-audit.json`:
- `artifacts/reference/legal/conditional-asset-audit.json`:
- `artifacts/reference/legal/notice-readiness-audit.json`:
- `artifacts/reference/legal/contributor-license-readiness-audit.json`:
- `artifacts/reference/legal/third-party-notice-candidate-audit.json`:
- `artifacts/reference/legal/apache-license-cutover-readiness-audit.json`:

## Required Approval Items

| Item | Required reviewer / owner | Decision | Date | Evidence / note |
| --- | --- | --- | --- | --- |
| Contributor / relicensing authority review | project owner + legal reviewer | pending |  |  |
| Root `NOTICE` text approval | legal reviewer | pending |  |  |
| Trademark boundary review | brand / trademark owner | pending |  |  |
| Third-party notice review | legal reviewer | pending |  |  |
| Apache-2.0 cutover readiness audit review | project owner | pending |  |  |

## Hold Points

Do not open or merge the actual cutover PR while any of the following remain true.

- any row above is still `pending`
- `apache-license-cutover-readiness-audit/v1` is not `ready`
- `third-party-notice-candidate-audit/v1` is `review-required`
- approved `NOTICE` text is not attached or linked

## Decision Record

- overall decision: pending
- approved for cutover: no
- decision date:
- approving owner:
- legal reviewer:
- notes:

## Open Questions / Follow-ups

- none recorded

## Related Documents

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md`
- `docs/project/APACHE-LICENSE-CUTOVER-READINESS.md`
- `docs/project/NOTICE-READINESS-AUDIT.md`
- `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`
- `docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md`
