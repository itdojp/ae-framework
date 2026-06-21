# Human maintainer review and waiver fixture

Raw fixture: `../human-waiver-review-output.json`

## Producer boundary

Human review is the only producer lane that can supply explicit policy override intent, but the waiver remains valid only when owner, reason, expiry, affected claim, and evidence link are traceable.

## Expected normalized routing

- `policy-decision/v1` for pass/report-only/waived/block disposition.
- `claim-evidence-manifest/v1` waiver entries for affected claims.
- `change-package/v2` for reviewed command evidence and affected files.

A waiver is not a tested, proved, or satisfied result.
