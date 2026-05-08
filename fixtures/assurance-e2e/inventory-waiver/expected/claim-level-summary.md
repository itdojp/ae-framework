# Claim-Level Assurance Summary

- schemaVersion: `claim-level-summary/v1`
- generatedAt: `2026-05-06T00:00:00.000Z`
- source: `itdojp/ae-framework` PR #3245
- refs: `main` → `feat/3245-assurance-e2e`

## Counts

| total | satisfied | tested | model-checked | proved | runtime-mitigated | waived | unresolved | failed | not-applicable | enforced | report-only |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 0 | 0 | 1 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 3 |

## Claims

| claim | state | target | achieved | decision | evidence | missing | waivers |
| --- | --- | --- | --- | --- | ---: | ---: | ---: |
| `manual-fraud-review` | waived | A3 | A2 | report-only/waived | 3 | 0 | 1 |
| `no-negative-balance` | model-checked | A3 | A2 | report-only/report-only | 5 | 1 | 0 |
| `no-negative-stock` | runtime-mitigated | A2 | A2 | report-only/pass | 7 | 0 | 0 |

## Missing evidence
- `no-negative-balance`
  - other: achievedLevel A2 is below targetLevel A3; additional evidence is required. (`change-package-v2:no-negative-balance:target-a3:achieved-a2`)

## Waivers / overrides
- `manual-fraud-review`: active, expires 2099-12-31, owner @team-risk (`change-package-v2:waiver:0:manual-fraud-review`)

