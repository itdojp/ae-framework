---
docRole: ssot
canonicalSource: docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md
lastVerified: '2026-03-13'
owner: project-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Apache License Cutover Playbook

## Purpose

This playbook defines the execution order, hold points, and rollback procedure for the Apache-2.0 cutover tracked by `#2623`.

It does not replace legal review. It connects deterministic factual audits to the human decisions required before changing the repository-standard license.

## Scope

This playbook covers the coordinated change set below.

- root `LICENSE`
- root `NOTICE`
- root `package.json` `license` field
- `README.md` license summary/link
- `CONTRIBUTING.md` inbound/outbound license policy
- `LICENSE-SCOPE.md`
- `TRADEMARKS.md`
- `THIRD_PARTY_NOTICES.md`

## Preconditions

The cutover PR should not start until all factual audits are regenerated from the same head SHA and reviewed.

### Required factual and approval audits

- Baseline audit refresh: `pnpm run license:audit:all`
- Approval record validation: `pnpm run license:audit:approval`
- Recommended final preflight before opening the cutover PR:
  - `pnpm run license:audit:precutover -- --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md`

### Required human review

- contributor/relicensing authority review
- NOTICE text approval
- trademark boundary review
- third-party/upstream notice review, if candidate audit reports any findings

## Hold points

The cutover remains blocked if any of the following hold.

- `apache-license-cutover-readiness-audit/v1` is `blocked`
- `apache-license-cutover-approval-readiness-audit/v1` is not `ready`
- `third-party-notice-candidate-audit/v1` reports `review-required`
- root `NOTICE` text is not approved
- contributor/legal review is incomplete

## Execution sequence

### 1. Regenerate all factual audits from a single head SHA

Use the suite command while the approval record is still being prepared.

```text
SOURCE_DATE_EPOCH=<unix-seconds> pnpm run license:audit:all
```

### 2. Freeze the legal decision inputs

Review the generated Markdown reports and record explicit human approval in `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md` for:

- contributor/relicensing authority
- root `NOTICE` text
- third-party notice candidates, if any
- trademark scope

Once the record is complete, run the final preflight command. It regenerates the six factual audits and then validates the approval record against the resulting cutover readiness audit. If the approval snapshot `head SHA` is older than the current cutover branch `HEAD`, the diff must stay within the cutover-allowed files only.

```text
SOURCE_DATE_EPOCH=<unix-seconds> pnpm run license:audit:precutover -- --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md
```

Use `--output-dir <path>` if the legal artifacts need to be generated into a non-default directory.

### 3. Prepare the cutover patch as one PR

The actual cutover PR should update the following in one changeset.

- replace root `LICENSE` with Apache-2.0 standard text
- add root `NOTICE`
- switch root `package.json` `license` from `MIT` to `Apache-2.0`
- update `README.md` summary if wording still mentions the old default license
- update `CONTRIBUTING.md` if inbound/outbound text still references the old default license
- regenerate the factual audits from the cutover head SHA

### 4. Validate the cutover PR

```text
node scripts/ci/validate-json.mjs
pnpm -s run check:doc-consistency
pnpm -s run check:ci-doc-index-consistency
SOURCE_DATE_EPOCH=<unix-seconds> pnpm run license:audit:precutover -- --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md
```

### 5. Post-merge verification

- confirm GitHub license detection reports Apache-2.0 on the repository page
- confirm `LICENSE-SCOPE.md`, `TRADEMARKS.md`, and `THIRD_PARTY_NOTICES.md` still match the merged head
- confirm the cutover readiness audit remains `ready` on the merged commit

## Rollback

If the cutover PR is merged and must be reverted, revert the full cutover changeset as one unit.

- restore root `LICENSE` to MIT
- remove root `NOTICE`
- restore root `package.json` `license` field to `MIT`
- restore any synchronized wording in `README.md` / `CONTRIBUTING.md`
- regenerate all factual audits from the rollback head SHA
- document why the cutover was reverted before opening a follow-up PR

## Notes

- `README.md` and `CONTRIBUTING.md` should only change in the actual cutover PR, not earlier. Their wording is part of the externally visible license statement.
- `NOTICE` should not be added before the cutover PR. The approved draft can exist in `docs/project/NOTICE-READINESS-AUDIT.md`, but the root file should only appear when the license switch is executed.
- Human sign-off should be captured in `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md` before the cutover PR is opened.
- This playbook does not decide legal feasibility. It only fixes the execution procedure once approvals exist.
