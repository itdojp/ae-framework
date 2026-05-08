# Security assurance boundary-case fixtures

These fixtures keep Security Assurance Lane edge cases reproducible at the CLI and contract boundary.

- `zero-finding.security-audit-responses.json`: proof-attempt fixture where every matched task reports `no-finding`; no `security-findings.json` is emitted.
- `multiple-review-records.security-review.json`: two review records for the same candidate finding, used to preserve review-history semantics.
- `trust-boundary-unknown.security-review.json`: review outcome where the trust-boundary gate remains `unknown`, keeping the candidate-first posture explicit.
