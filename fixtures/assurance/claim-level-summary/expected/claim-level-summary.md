# Claim-Level Assurance Summary

- schemaVersion: `claim-level-summary/v1`
- generatedAt: `2026-05-08T00:00:00.000Z`
- source: `itdojp/ae-framework` PR #3307
- refs: `main` → `feat/3307-claim-level-summary`

## Counts

| total | satisfied | tested | model-checked | proved | runtime-mitigated | waived | unresolved | failed | not-applicable | enforced | report-only |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 9 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 9 |

## Claims

| claim | state | target | achieved | decision | evidence | missing | waivers |
| --- | --- | --- | --- | --- | ---: | ---: | ---: |
| `balance-proved` | proved | A4 | A4 | report-only/pass | 1 | 0 | 0 |
| `inventory-model` | model-checked | A3 | A3 | report-only/pass | 1 | 0 | 0 |
| `manual-waiver` | waived | A3 | A1 | report-only/waived | 1 | 1 | 1 |
| `policy-satisfied` | satisfied | A1 | A1 | report-only/pass | 1 | 0 | 0 |
| `reservation-tested` | tested | A2 | A2 | report-only/pass | 1 | 0 | 0 |
| `rollout-runtime` | runtime-mitigated | A3 | A2 | report-only/report-only | 1 | 1 | 0 |
| `strict-proof-failure` | failed | A4 | A1 | report-only/report-only | 2 | 1 | 0 |
| `ui-out-of-scope` | not-applicable | A1 | A0 | report-only/report-only | 0 | 0 | 0 |
| `unresolved-model` | unresolved | A3 | A1 | report-only/report-only | 0 | 1 | 0 |

## Missing evidence
- `manual-waiver`
  - model: Automated fraud model validation evidence is not linked. (`missing-model:manual-waiver`)
- `rollout-runtime`
  - proof: Proof evidence is not yet linked for the rollout guard claim. (`missing-proof:rollout-runtime`)
- `strict-proof-failure`
  - proof: Discharged proof evidence is required for strict release. (`missing-discharged-proof:strict-proof`)
- `unresolved-model`
  - model: Model reconciliation summary is absent. (`missing-model:unresolved-model`)

## Waivers / overrides
- `manual-waiver`: active, expires 2026-06-30, owner @team-risk (`override-manual-waiver-2026-06`)

## Applicability exclusions
- `ui-out-of-scope`: UI-only animation claim is outside the backend release scope. (scope: backend release)

