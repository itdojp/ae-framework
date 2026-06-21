# Scope Drift Assurance Demo Review

> Reviewer-first Markdown generated from schema-backed assurance artifacts. It summarizes evidence and gaps; it does not approve, prove, or merge a PR.

- generatedAt: `2026-06-21T00:00:00.000Z`
- recommendedReviewerAction: `review-boundary-map`
- reason: Boundary Map status is drift; treat it as a design-boundary evidence gap, not a proof failure.

## Artifact inputs

| artifact | path | status |
| --- | --- | --- |
| producer-normalization-summary | artifacts/agents/scope-drift-demo/producer-normalization-summary.json | present |
| assurance-summary | artifacts/assurance/scope-drift-demo/assurance-summary.json | present |
| policy-gate-summary | artifacts/policy/scope-drift-demo/policy-gate-summary.normal.json | present |
| boundary-map-summary | artifacts/context-pack/scope-drift-demo/boundary-map-summary.json | present |
| claim-evidence-manifest | artifacts/assurance/claim-evidence-manifest.json | missing |
| verify-lite-run-summary | artifacts/verify-lite/verify-lite-run-summary.json | missing |

## Producer / task scope

Producer output is displayed as report-only input. It is never rendered as approval.

| artifact | producer | category | raw signals | changed files | commands | missing evidence | report-only findings | control-plane judgment |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| artifacts/agents/scope-drift-demo/producer-normalization-summary.json | Codex CLI local task with scope drift | local-agent | 5 | 4 | 3 | 2 | 4 | not-emitted |

### Changed-file scope

| path | role | expected artifact |
| --- | --- | --- |
| docs/inventory/reservation-audit.md | intended documentation change from the sample Issue | assurance-summary/v1 |
| tests/unit/inventory/reservation-audit.test.ts | focused test evidence for the intended documentation update | claim-evidence-manifest/v1 |
| examples/assurance-control-plane/scope-drift-demo/README.md | reviewer-facing scenario documentation | assurance-summary/v1 |
| src/payments/settlement-retry.ts | out-of-scope producer change that requires reviewer disposition | boundary-map-summary/v1 |

## Boundary / scope status

A missing boundary artifact is shown as `missing` / `not provided`; absence is not rendered as boundary-ok.

| artifact | status | review status | findings | evidence kind | decision | interpretation |
| --- | --- | --- | --- | --- | --- | --- |
| artifacts/context-pack/scope-drift-demo/boundary-map-summary.json | drift | boundary map drift | 2 | design-boundary | report-only-evidence-gap | Scope drift is design-boundary evidence. It is not proof evidence and is not a proof failure by itself. |

## Claims and evidence status

`tested`, `model-checked`, `proved`, `waived`, `unresolved`, and `runtime-mitigated` remain separate artifact states. This renderer shows source artifact status and evidence kinds without collapsing them into approval.

| claim | assurance status | manifest status | evidence kinds | missing lanes | missing evidence kinds | missing evidence refs | waiver refs | runtime controls |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| scope-drift-within-declared-boundary | warning | not provided | none | spec | boundary-map | 0 | 0 | 0 |

## Missing evidence / unresolved claims

| source | artifact | claim or evidence | review note |
| --- | --- | --- | --- |
| producer-summary | artifacts/agents/scope-drift-demo/producer-normalization-summary.json | pnpm -s run context-pack:verify-boundary-map | Command evidence is not complete: pnpm -s run context-pack:verify-boundary-map (not-run-in-producer-output) |
| producer-summary | artifacts/agents/scope-drift-demo/producer-normalization-summary.json | scope-drift-within-declared-boundary | Claim has no supporting evidence list: scope-drift-within-declared-boundary |
| assurance-summary | artifacts/assurance/scope-drift-demo/assurance-summary.json | scope-drift-within-declared-boundary | status=warning; missingLanes=spec; missingEvidenceKinds=boundary-map; warnings=insufficient-independent-lanes, missing-spec-derived-evidence |

## Waivers / runtime controls

Waived and runtime-mitigated claims require explicit reviewer attention; they are not counted as satisfied proof.

| claim | waiver/control | status | owner | expires | source |
| --- | --- | --- | --- | --- | --- |
| not provided | not provided | not provided | not provided | not provided | not provided |

## Policy decision / report-only vs blocking

| artifact | risk label | assurance mode | assurance result | ok | errors | warnings |
| --- | --- | --- | --- | --- | --- | --- |
| artifacts/policy/scope-drift-demo/policy-gate-summary.normal.json | risk:low | report-only | report-only | true | 0 | 2 |

## Reviewer action list

- Start with this Markdown before raw logs; then open `artifacts/assurance/scope-drift-demo/assurance-summary.json` and `artifacts/policy/scope-drift-demo/policy-gate-summary.normal.json`.
- Treat producer assertions as evidence input only; do not treat producer conclusion as approval.
- Follow recommendedReviewerAction=`review-boundary-map`: Boundary Map status is drift; treat it as a design-boundary evidence gap, not a proof failure.
- Resolve or explicitly accept the listed missing evidence / unresolved claim rows before using the surface as release evidence.
- Claim evidence manifest is missing or not provided; do not infer claim-level satisfied/waived status from absence.
- For ordinary PRs, report-only findings remain reviewer context; for risk/high-assurance PRs, follow policy decision result=`report-only` mode=`report-only`.

## Interpretation guardrails

- Producer conclusion is not approval.
- Green baseline checks are not proof for high-assurance claims.
- Missing optional artifacts must stay visible as `missing` / `not provided`.
- Policy escalation depends on risk labels, assurance profile, and selected critical claims, not on the agent vendor.
