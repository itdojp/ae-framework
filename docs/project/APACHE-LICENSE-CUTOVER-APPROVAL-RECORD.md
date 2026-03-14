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

- head SHA: 770516147a0c6c9ff0999025109cd22e24ac374f
- `artifacts/reference/legal/license-scope-audit.json`: `artifacts/reference/legal/license-scope-audit.json`
- `artifacts/reference/legal/conditional-asset-audit.json`: `artifacts/reference/legal/conditional-asset-audit.json`
- `artifacts/reference/legal/notice-readiness-audit.json`: `artifacts/reference/legal/notice-readiness-audit.json`
- `artifacts/reference/legal/contributor-license-readiness-audit.json`: `artifacts/reference/legal/contributor-license-readiness-audit.json`
- `artifacts/reference/legal/third-party-notice-candidate-audit.json`: `artifacts/reference/legal/third-party-notice-candidate-audit.json`
- `artifacts/reference/legal/apache-license-cutover-readiness-audit.json`: `artifacts/reference/legal/apache-license-cutover-readiness-audit.json`

This baseline records the reviewed head for the approval snapshot. The snapshot was refreshed on the immediate pre-cutover head after `license:audit:precutover` passed. If any additional commits are added before opening the actual cutover PR, rerun `pnpm run license:audit:precutover -- --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md` and refresh the recorded head SHA again.

## Required Approval Items

| Item | Required reviewer / owner | Decision | Date | Evidence / note |
| --- | --- | --- | --- | --- |
| Contributor / relicensing authority review | project owner + legal reviewer | approved | 2026-03-14 | ITDO Inc. 管理下の first-party 資産を対象とし、代表 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が project owner 兼 legal reviewer として確認。`artifacts/reference/legal/contributor-license-readiness-audit.json` を根拠に cutover 実施可と判断。 |
| Root `NOTICE` text approval | legal reviewer | approved | 2026-03-14 | ITDO Inc. の legal reviewer として代表 太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が `docs/project/NOTICE-READINESS-AUDIT.md` の `Approved root NOTICE text` と `artifacts/reference/legal/notice-readiness-audit.json` を確認し、root `NOTICE` の承認済み文面を承認。 |
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
- notes: 現時点では 1 人運用のため、project owner / legal reviewer / brand-trademark owner の各責務は ITDO Inc. 代表の太田和彦 / Kazuhiko OOTA (passport romanization: Kazuhiko Ota) が兼務して判断した。本記録は reviewed head `770516147a0c6c9ff0999025109cd22e24ac374f` に対する approval snapshot であり、この head で `pnpm run license:audit:precutover -- --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md` の成功を確認した。actual cutover PR を開く前にさらに commit が追加される場合は、同コマンドを再実行して reviewed head を更新する。

## Open Questions / Follow-ups

- none recorded

## Related Documents

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md`
- `docs/project/APACHE-LICENSE-CUTOVER-READINESS.md`
- `docs/project/NOTICE-READINESS-AUDIT.md`
- `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`
- `docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md`
