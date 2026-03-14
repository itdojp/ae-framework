---
docRole: ssot
canonicalSource: docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md
lastVerified: '2026-03-14'
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

Record the reviewed commit and audit artifacts used for the decision snapshot.

- head SHA: c6da4ed5ee04bab0330a3f35a63c0cc30b280bf7
- `artifacts/reference/legal/license-scope-audit.json`: `artifacts/reference/legal/license-scope-audit.json`
- `artifacts/reference/legal/conditional-asset-audit.json`: `artifacts/reference/legal/conditional-asset-audit.json`
- `artifacts/reference/legal/notice-readiness-audit.json`: `artifacts/reference/legal/notice-readiness-audit.json`
- `artifacts/reference/legal/contributor-license-readiness-audit.json`: `artifacts/reference/legal/contributor-license-readiness-audit.json`
- `artifacts/reference/legal/third-party-notice-candidate-audit.json`: `artifacts/reference/legal/third-party-notice-candidate-audit.json`
- `artifacts/reference/legal/apache-license-cutover-readiness-audit.json`: `artifacts/reference/legal/apache-license-cutover-readiness-audit.json`

This baseline records the reviewed head for the approval snapshot. If follow-up documentation-only commits are added after the snapshot is recorded, rerun `pnpm run license:audit:precutover -- --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md` on the actual cutover branch and refresh the recorded head SHA before opening the cutover PR.

## Required Approval Items

| Item | Required reviewer / owner | Decision | Date | Evidence / note |
| --- | --- | --- | --- | --- |
| Contributor / relicensing authority review | project owner + legal reviewer | approved | 2026-03-14 | ITDO Inc. 管理下の first-party 資産を対象とし、代表 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が project owner 兼 legal reviewer として確認。`artifacts/reference/legal/contributor-license-readiness-audit.json` を根拠に cutover 実施可と判断。 |
| Root `NOTICE` text approval | legal reviewer | approved | 2026-03-14 | ITDO Inc. の legal reviewer として代表 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が `docs/project/NOTICE-READINESS-AUDIT.md` の `Proposed root NOTICE draft` と `artifacts/reference/legal/notice-readiness-audit.json` を確認し、root `NOTICE` 草案を承認。 |
| Trademark boundary review | brand / trademark owner | approved | 2026-03-14 | ITDO Inc. の brand / trademark owner として代表 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が確認。`ae-framework`、`ITDO`、ロゴ、製品名、ブランド表示は Apache-2.0 の対象外として `TRADEMARKS.md` で別管理する方針を承認。 |
| Third-party notice review | legal reviewer | approved | 2026-03-14 | ITDO Inc. の legal reviewer として代表 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が `artifacts/reference/legal/third-party-notice-candidate-audit.json` を確認。現時点で `status=no-candidates` であり、追加の third-party / upstream notice 候補なしと判断。 |
| Apache-2.0 cutover readiness audit review | project owner | approved | 2026-03-14 | ITDO Inc. の project owner として代表 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が `artifacts/reference/legal/apache-license-cutover-readiness-audit.json` を確認。`status=human-review-required` かつ factual blocker なしであり、人手承認で cutover 実施条件を満たすと判断。 |

## Hold Points

Do not open or merge the actual cutover PR while any of the following remain true.

- any row above is still `pending`
- `apache-license-cutover-readiness-audit/v1` is `blocked`
- `apache-license-cutover-approval-readiness-audit/v1` is not `ready`
- `third-party-notice-candidate-audit/v1` is `review-required`
- approved `NOTICE` text is not attached or linked

## Decision Record

- overall decision: approved
- approved for cutover: yes
- decision date: 2026-03-14
- approving owner: 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota), Representative Director, ITDO Inc.
- legal reviewer: 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota), Representative Director, ITDO Inc.
- notes: 現時点では 1 人運用のため、project owner / legal reviewer / brand-trademark owner の各責務は ITDO Inc. 代表の太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が兼務して判断した。本記録は reviewed head `c6da4ed5ee04bab0330a3f35a63c0cc30b280bf7` に対する approval snapshot であり、actual cutover 実行前には cutover branch 上で `pnpm run license:audit:precutover -- --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md` を再実行し、同一 head で再確認する。後続の文書更新で PR head が進んだ場合でも、この snapshot 自体は reviewed head を保持する。

## Open Questions / Follow-ups

- none recorded

## Related Documents

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md`
- `docs/project/APACHE-LICENSE-CUTOVER-READINESS.md`
- `docs/project/NOTICE-READINESS-AUDIT.md`
- `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`
- `docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md`
