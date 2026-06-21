# BYO-Agent Assurance Demo Review

> Reviewer-first Markdown generated from schema-backed assurance artifacts. It summarizes evidence and gaps; it does not approve, prove, or merge a PR.

- generatedAt: `2026-06-21T00:00:00.000Z`
- recommendedReviewerAction: `review-unresolved-claims`
- reason: Assurance warning claims=1, unresolved/partial manifest claims=0, claims with missing evidence=0.

## Artifact inputs

| artifact | path | status |
| --- | --- | --- |
| producer-normalization-summary | artifacts/agents/agent-assurance-demo/producer-normalization-summary.json | present |
| assurance-summary | artifacts/assurance/agent-assurance-demo/assurance-summary.json | present |
| policy-gate-summary | artifacts/policy/agent-assurance-demo/policy-gate-summary.json | present |
| boundary-map-summary | artifacts/context-pack/agent-assurance-demo/boundary-map-summary.json | missing |
| claim-evidence-manifest | artifacts/assurance/claim-evidence-manifest.json | missing |
| verify-lite-run-summary | artifacts/verify-lite/agent-assurance-demo/verify-lite-run-summary.json | present |

## Producer / task scope

Producer output is displayed as report-only input. It is never rendered as approval.

| artifact | producer | category | raw signals | changed files | commands | missing evidence | report-only findings | control-plane judgment |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| artifacts/agents/agent-assurance-demo/producer-normalization-summary.json | Codex CLI local task | local-agent | 4 | 3 | 3 | 2 | 5 | not-emitted |

### Changed-file scope

| path | role | expected artifact |
| --- | --- | --- |
| src/inventory/reservation-audit.ts | sample source change described by the producer | change-package/v2 |
| tests/unit/inventory/reservation-audit.test.ts | focused test evidence described by the producer | claim-evidence-manifest/v1 |
| docs/inventory/reservation-audit.md | reviewer-facing explanation described by the producer | assurance-summary/v1 |

## Boundary / scope status

A missing boundary artifact is shown as `missing` / `not provided`; absence is not rendered as boundary-ok.

| artifact | status | review status | findings | evidence kind | decision | interpretation |
| --- | --- | --- | --- | --- | --- | --- |
| none | not-provided | none | 0 | not provided | from assurance-summary reviewSurface | No boundary-map summary was provided. |

## Selected critical claims

Only selected `high` / `critical` claims are promoted to high-assurance review. Required evidence kinds are displayed separately from claim status.

| claim | criticality | target level | required lanes | required evidence kinds | assurance status | manifest status |
| --- | --- | --- | --- | --- | --- | --- |
| no-negative-stock | high | A3 | behavior, model, spec | counterexample-closed, product-coproduct, property | warning | not provided |

## Claims and evidence status

`tested`, `model-checked`, `proved`, `waived`, `unresolved`, and `runtime-mitigated` remain separate artifact states. This renderer shows source artifact status and evidence kinds without collapsing them into approval.

| claim | assurance status | manifest status | evidence kinds | missing lanes | missing evidence kinds | missing evidence refs | waiver refs | runtime controls |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| no-negative-stock | warning | not provided | none | spec, behavior, model | counterexample-closed, product-coproduct, property | 0 | 0 | 0 |

## Missing evidence / unresolved claims

| source | artifact | claim or evidence | review note |
| --- | --- | --- | --- |
| producer-summary | artifacts/agents/agent-assurance-demo/producer-normalization-summary.json | pnpm -s run check:schemas | Command evidence is not complete: pnpm -s run check:schemas (not-run-in-producer-output) |
| producer-summary | artifacts/agents/agent-assurance-demo/producer-normalization-summary.json | schema-validation-evidence-present | Claim has no supporting evidence list: schema-validation-evidence-present |
| assurance-summary | artifacts/assurance/agent-assurance-demo/assurance-summary.json | no-negative-stock | status=warning; missingLanes=spec, behavior, model; missingEvidenceKinds=counterexample-closed, product-coproduct, property; warnings=insufficient-independent-lanes, missing-spec-derived-evidence |

## Waivers / runtime controls

Waived and runtime-mitigated claims require explicit reviewer attention; they are not counted as satisfied proof.

| claim | waiver/control | status | owner | expires | source |
| --- | --- | --- | --- | --- | --- |
| not provided | not provided | not provided | not provided | not provided | not provided |

## Policy decision / report-only vs blocking

| artifact | risk label | assurance mode | assurance result | ok | errors | warnings |
| --- | --- | --- | --- | --- | --- | --- |
| artifacts/policy/agent-assurance-demo/policy-gate-summary.json | risk:low | report-only | report-only | true | 0 | 0 |

## Reviewer action list

- Start with this Markdown before raw logs; then open `artifacts/assurance/agent-assurance-demo/assurance-summary.json` and `artifacts/policy/agent-assurance-demo/policy-gate-summary.json`.
- Treat producer assertions as evidence input only; do not treat producer conclusion as approval.
- Follow recommendedReviewerAction=`review-unresolved-claims`: Assurance warning claims=1, unresolved/partial manifest claims=0, claims with missing evidence=0.
- Resolve or explicitly accept the listed missing evidence / unresolved claim rows before using the surface as release evidence.
- Boundary artifact is missing or not provided; record why scope drift is not assessed, or generate the Boundary Map summary.
- Claim evidence manifest is missing or not provided; do not infer claim-level satisfied/waived status from absence.
- For ordinary PRs, report-only findings remain reviewer context; for risk/high-assurance PRs, follow policy decision result=`report-only` mode=`report-only`.

## Interpretation guardrails

- Producer conclusion is not approval.
- Green baseline checks are not proof for high-assurance claims.
- Missing optional artifacts must stay visible as `missing` / `not provided`.
- Policy escalation depends on risk labels, assurance profile, and selected critical claims, not on the agent vendor.
