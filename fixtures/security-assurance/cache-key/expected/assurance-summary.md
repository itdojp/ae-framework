# Assurance Summary

- generatedAt: 2026-05-07T00:00:00.000Z
- claimCount: 3
- satisfiedClaims: 0
- warningClaims: 3
- warningCount: 2
- unlinkedCounterexamples: 0

## Claim status

| claim | status | required lanes | observed lanes | missing lanes | warnings |
| --- | --- | --- | --- | --- | --- |
| SEC-CLAIM-001 | warning | adversarial, spec | spec, adversarial |  | unresolved-critical-counterexample |
| SEC-CLAIM-002 | warning | spec | spec |  |  |
| SEC-CLAIM-003 | warning | adversarial, spec | spec, adversarial |  |  |

## Lane coverage

| lane | required claims | observed claims |
| --- | --- | --- |
| spec | 3 | 3 |
| behavior | 0 | 0 |
| adversarial | 2 | 2 |
| model | 0 | 0 |
| proof | 0 | 0 |
| runtime | 0 | 0 |

## Warnings

- unresolved-critical-counterexample: claim=SEC-CLAIM-001 artifact=artifacts/security-assurance/cache-key/security-findings.json High/critical security finding SEC-FINDING-001 remains needsHumanReview.
- unresolved-critical-counterexample: claim=SEC-CLAIM-001 Critical claim still has unresolved counterexamples.
