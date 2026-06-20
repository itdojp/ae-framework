# Assurance Summary

- generatedAt: 2026-05-07T00:00:00.000Z
- claimCount: 3
- satisfiedClaims: 0
- warningClaims: 3
- warningCount: 2
- unlinkedCounterexamples: 0

## Reviewer decision surface

- recommendedReviewerAction: review-unresolved-claims
- reason: Assurance warning claims=3, unresolved/partial manifest claims=0, claims with missing evidence=0.
- manifestClaims: satisfied=0, partial=0, waived=0, unresolved=0, failed=0
- assuranceSummaryClaims: satisfied=0, warning=3
- missingEvidenceClaims: 0
- activeWaivers: 0
- producerSignals: not-provided (reportOnlyFindings=0, missingEvidence=0)
- boundaryMap: not-provided (findings=0)
- policyDecision: not-provided (mode=n/a)

Interpretation notes:

- Producer assertions remain producer assertions; control-plane judgment must come from reviewed, schema-backed evidence and policy artifacts.
- tested and proved are distinct evidence outcomes; runtime-mitigated is not proof.
- waived is an explicit exception state and must not be counted as satisfied.
- This review surface helps reviewers identify support and gaps; it is not an automatic merge approval.

## Claim status

| claim | type | status | required lanes | observed lanes | missing lanes | assumption handling | warnings |
| --- | --- | --- | --- | --- | --- | --- | --- |
| SEC-CLAIM-001 | invariant | warning | adversarial, spec | spec, adversarial |  | n/a | unresolved-critical-counterexample |
| SEC-CLAIM-002 | precondition | warning | spec | spec |  | n/a |  |
| SEC-CLAIM-003 | assumption | warning | adversarial, spec | spec, adversarial |  | SEC-FINDING-002:residual-risk |  |

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
