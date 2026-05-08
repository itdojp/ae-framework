# Claim Evidence Manifest

- schemaVersion: claim-evidence-manifest/v1
- generatedAt: 2026-05-06T00:00:00.000Z
- sourceArtifacts: 4/8 present
- claims: 3 total; 1 satisfied, 1 partial, 1 waived, 0 unresolved
- missingEvidenceRefs: 1
- waiverRefs: 1

## Source artifacts

| id | kind | present | required | path | schemaVersion |
| --- | --- | --- | --- | --- | --- |
| assurance-summary | assurance-summary | true | true | fixtures/assurance-e2e/inventory-waiver/inputs/assurance-summary.json | assurance-summary/v1 |
| change-package-v2 | change-package-v2 | true | false | fixtures/assurance-e2e/inventory-waiver/inputs/change-package-v2.json | change-package/v2 |
| quality-scorecard | quality-scorecard | true | false | fixtures/assurance-e2e/inventory-waiver/inputs/quality-scorecard.json | quality-scorecard/v1 |
| verify-lite-run-summary | verify-lite-run-summary | true | false | fixtures/assurance-e2e/inventory-waiver/inputs/verify-lite-run-summary.json | 1.0.0 |
| trace-bundle | trace-bundle | false | false | n/a | n/a |
| security-claims | security-claim | false | false | n/a | n/a |
| security-findings | security-finding | false | false | n/a | n/a |
| security-review | security-review | false | false | n/a | n/a |

## Claims

| claim | securityType | criticality | target | achieved | status | evidence | missing | waivers | assumptionHandling | externalIds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| manual-fraud-review | n/a | medium | A3 | A2 | waived | 3 | 0 | 1 | n/a | n/a |
| no-negative-balance | n/a | high | A3 | A2 | partial | 5 | 1 | 0 | n/a | n/a |
| no-negative-stock | n/a | high | A2 | A2 | satisfied | 7 | 0 | 0 | n/a | n/a |

## External IDs

- none

## Assumption handling

- none

## Missing evidence

- no-negative-balance: change-package-v2:no-negative-balance:target-a3:achieved-a2 (other) — achievedLevel A2 is below targetLevel A3; additional evidence is required.

## Waivers

- manual-fraud-review: change-package-v2:waiver:0:manual-fraud-review status=active owner=@team-risk expires=2099-12-31 — Manual fraud review is active while automated model validation evidence is being collected.
