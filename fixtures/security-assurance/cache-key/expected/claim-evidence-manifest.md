# Claim Evidence Manifest

- schemaVersion: claim-evidence-manifest/v1
- generatedAt: 2026-05-07T00:00:00.000Z
- sourceArtifacts: 4/8 present
- claims: 3 total; 0 satisfied, 3 partial, 0 waived, 0 unresolved
- securityFindings: 2 total; highOrCriticalOpen=1, needsHumanReview=1, outOfScope=1, rejected=0
- missingEvidenceRefs: 4
- waiverRefs: 0

## Source artifacts

| id | kind | present | required | path | schemaVersion |
| --- | --- | --- | --- | --- | --- |
| assurance-summary | assurance-summary | true | true | artifacts/security-assurance/cache-key/assurance-summary.json | assurance-summary/v1 |
| change-package-v2 | change-package-v2 | false | false | n/a | n/a |
| quality-scorecard | quality-scorecard | false | false | n/a | n/a |
| verify-lite-run-summary | verify-lite-run-summary | false | false | n/a | n/a |
| trace-bundle | trace-bundle | false | false | n/a | n/a |
| security-claims | security-claim | true | false | artifacts/security-assurance/cache-key/security-claims.json | security-claim/v1 |
| security-findings | security-finding | true | false | artifacts/security-assurance/cache-key/security-findings.json | security-finding/v1 |
| security-review | security-review | true | false | artifacts/security-assurance/cache-key/security-review.json | security-review/v1 |

## Claims

| claim | criticality | target | achieved | status | evidence | missing | waivers | externalIds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| sec-claim-001 | high | A2 | A1 | partial | 6 | 2 | 0 | security-claim:SEC-CLAIM-001 (security-claims) |
| sec-claim-002 | medium | A1 | A0 | partial | 2 | 1 | 0 | security-claim:SEC-CLAIM-002 (security-claims) |
| sec-claim-003 | low | A2 | A0 | partial | 6 | 1 | 0 | security-claim:SEC-CLAIM-003 (security-claims) |

## External IDs

| claim | subject | externalId | artifactPath |
| --- | --- | --- | --- |
| sec-claim-001 | claim | security-claim:SEC-CLAIM-001 (security-claims) | artifacts/security-assurance/cache-key/security-claims.json#/claims/0 |
| sec-claim-001 | evidence:security-claims:sec-claim-001 | security-claim:SEC-CLAIM-001 (security-claims) | artifacts/security-assurance/cache-key/security-claims.json#/claims/0 |
| sec-claim-001 | evidence:security-findings:sec-finding-001 | security-finding:SEC-FINDING-001 (security-findings) | artifacts/security-assurance/cache-key/security-findings.json#/findings/0 |
| sec-claim-001 | evidence:security-review:sec-finding-001:0 | security-review:SEC-FINDING-001:review:0 (security-review) | artifacts/security-assurance/cache-key/security-review.json#/reviews/0 |
| sec-claim-002 | claim | security-claim:SEC-CLAIM-002 (security-claims) | artifacts/security-assurance/cache-key/security-claims.json#/claims/1 |
| sec-claim-002 | evidence:security-claims:sec-claim-002 | security-claim:SEC-CLAIM-002 (security-claims) | artifacts/security-assurance/cache-key/security-claims.json#/claims/1 |
| sec-claim-003 | claim | security-claim:SEC-CLAIM-003 (security-claims) | artifacts/security-assurance/cache-key/security-claims.json#/claims/2 |
| sec-claim-003 | evidence:security-claims:sec-claim-003 | security-claim:SEC-CLAIM-003 (security-claims) | artifacts/security-assurance/cache-key/security-claims.json#/claims/2 |
| sec-claim-003 | evidence:security-findings:sec-finding-002 | security-finding:SEC-FINDING-002 (security-findings) | artifacts/security-assurance/cache-key/security-findings.json#/findings/1 |
| sec-claim-003 | evidence:security-review:sec-finding-002:1 | security-review:SEC-FINDING-002:review:1 (security-review) | artifacts/security-assurance/cache-key/security-review.json#/reviews/1 |

## Missing evidence

- sec-claim-001: assurance-summary:sec-claim-001:missing-kind:counterexample-closed (adversarial) — Required evidence kind 'counterexample-closed' is not linked for this claim.
- sec-claim-001: security-human-review:sec-finding-001 (manual) — high severity security finding SEC-FINDING-001 is needs-human-review; human review or remediation evidence is required before treating it as supported.
- sec-claim-002: assurance-summary:sec-claim-002:missing-kind:schema (spec) — Required evidence kind 'schema' is not linked for this claim.
- sec-claim-003: assurance-summary:sec-claim-003:missing-kind:counterexample-closed (adversarial) — Required evidence kind 'counterexample-closed' is not linked for this claim.

## Security findings

- claims: 3
- findings: 2
- reviews: 2
- needsHumanReview: 1
- highOrCriticalOpen: 1
- outOfScope: 1
- rejected: 0

## Waivers

- none
