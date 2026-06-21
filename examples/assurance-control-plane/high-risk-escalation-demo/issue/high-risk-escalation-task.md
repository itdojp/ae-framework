# Sample Issue: tenant isolation high-risk claim escalation

Issue: fixture-only ACP-085 scenario

## Request

Update the tenant-isolation authorization policy for account-read requests and document the reviewer-facing evidence needed before merge.

## Risk framing

This is a selected high-risk domain because a tenant-isolation regression can expose another tenant's account data. The reviewer should not require heavy verification for every ordinary PR, but should require stronger evidence for the selected critical claim below.

## Selected critical claims

- `tenant-isolation-enforced-before-account-read`: Every account-read request is denied unless the authenticated tenant id matches the account tenant id before the repository read occurs.
- `tenant-isolation-waiver-has-reviewable-metadata`: Any temporary exception for the selected tenant-isolation claim has owner, reason, expiry, affected claim id, and an evidence link.

## Expected reviewer behavior

- Fast-lane documentation/test changes stay report-only.
- `risk:high` requires human disposition and a plan artifact.
- `enforce-assurance` turns missing required tenant-isolation evidence or incomplete waiver metadata into a blocking assurance result.
