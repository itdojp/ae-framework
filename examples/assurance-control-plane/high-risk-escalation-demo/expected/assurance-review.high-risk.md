# High-Risk Escalation Assurance Demo Review — High-Risk Strict Lane

> Reviewer-first Markdown generated from schema-backed assurance artifacts. It summarizes evidence and gaps; it does not approve, prove, or merge a PR.

- generatedAt: `2026-06-21T00:00:00.000Z`
- recommendedReviewerAction: `review-unresolved-claims`
- reason: Assurance warning claims=2, unresolved/partial manifest claims=1, claims with missing evidence=2.

## Artifact inputs

| artifact | path | status |
| --- | --- | --- |
| producer-normalization-summary | artifacts/agents/high-risk-escalation-demo/producer-normalization-summary.json | present |
| assurance-summary | artifacts/assurance/high-risk-escalation-demo/assurance-summary.json | present |
| policy-gate-summary | artifacts/policy/high-risk-escalation-demo/policy-gate-summary.high-risk.json | present |
| boundary-map-summary | artifacts/context-pack/high-risk-escalation-demo/boundary-map-summary.json | missing |
| claim-evidence-manifest | artifacts/assurance/high-risk-escalation-demo/claim-evidence-manifest.json | present |
| verify-lite-run-summary | artifacts/verify-lite/verify-lite-run-summary.json | missing |

## Producer / task scope

Producer output is displayed as report-only input. It is never rendered as approval.

| artifact | producer | category | raw signals | changed files | commands | missing evidence | report-only findings | control-plane judgment |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| artifacts/agents/high-risk-escalation-demo/producer-normalization-summary.json | Codex CLI local task with tenant-isolation claim gaps | local-agent | 5 | 3 | 4 | 4 | 6 | not-emitted |

### Changed-file scope

| path | role | expected artifact |
| --- | --- | --- |
| auth/tenant-isolation-policy.ts | fixture-only high-risk tenant isolation policy change | claim-evidence-manifest/v1 |
| tests/unit/auth/tenant-isolation-policy.test.ts | focused behavior evidence supplied by the producer | assurance-summary/v1 |
| examples/assurance-control-plane/high-risk-escalation-demo/README.md | reviewer-facing escalation documentation | assurance-summary/v1 |

## Boundary / scope status

A missing boundary artifact is shown as `missing` / `not provided`; absence is not rendered as boundary-ok.

| artifact | status | review status | findings | evidence kind | decision | interpretation |
| --- | --- | --- | --- | --- | --- | --- |
| none | not-provided | none | 0 | not provided | from assurance-summary reviewSurface | No boundary-map summary was provided. |

## Selected critical claims

Only selected `high` / `critical` claims are promoted to high-assurance review. Required evidence kinds are displayed separately from claim status.

| claim | criticality | target level | required lanes | required evidence kinds | assurance status | manifest status |
| --- | --- | --- | --- | --- | --- | --- |
| tenant-isolation-enforced-before-account-read | critical | A3 | adversarial, behavior, runtime, spec | property, runtime-control, schema, unit | warning | partial |
| tenant-isolation-waiver-has-reviewable-metadata | high | A2 | runtime, spec | runtime-control, waiver | warning | waived |

## Claims and evidence status

`tested`, `model-checked`, `proved`, `waived`, `unresolved`, and `runtime-mitigated` remain separate artifact states. This renderer shows source artifact status and evidence kinds without collapsing them into approval.

| claim | assurance status | manifest status | evidence kinds | missing lanes | missing evidence kinds | missing evidence refs | waiver refs | runtime controls |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| tenant-isolation-enforced-before-account-read | warning | partial | spec, behavior | spec, behavior, adversarial, runtime | property, runtime-control, schema, unit | 2 | 0 | 0 |
| tenant-isolation-waiver-has-reviewable-metadata | warning | waived | none | spec, runtime | runtime-control, waiver | 1 | 1 | 0 |

## Missing evidence / unresolved claims

| source | artifact | claim or evidence | review note |
| --- | --- | --- | --- |
| producer-summary | artifacts/agents/high-risk-escalation-demo/producer-normalization-summary.json | pnpm -s exec vitest run tests/property/auth/tenant-isolation-cross-tenant.test.ts --reporter dot | Command evidence is not complete: pnpm -s exec vitest run tests/property/auth/tenant-isolation-cross-tenant.test.ts --reporter dot (not-run-in-producer-output) |
| producer-summary | artifacts/agents/high-risk-escalation-demo/producer-normalization-summary.json | node scripts/runtime/validate-tenant-isolation-control.mjs | Command evidence is not complete: node scripts/runtime/validate-tenant-isolation-control.mjs (not-run-in-producer-output) |
| producer-summary | artifacts/agents/high-risk-escalation-demo/producer-normalization-summary.json | tenant-isolation-waiver-has-reviewable-metadata | Claim has no supporting evidence list: tenant-isolation-waiver-has-reviewable-metadata |
| producer-summary | artifacts/agents/high-risk-escalation-demo/producer-normalization-summary.json | tenant-isolation-waiver-has-reviewable-metadata | Waiver metadata is incomplete for claim tenant-isolation-waiver-has-reviewable-metadata: waiver.owner, waiver.reason, waiver.expiresAt |
| assurance-summary | artifacts/assurance/high-risk-escalation-demo/assurance-summary.json | tenant-isolation-enforced-before-account-read | status=warning; missingLanes=spec, behavior, adversarial, runtime; missingEvidenceKinds=property, runtime-control, schema, unit; warnings=insufficient-independent-lanes, missing-spec-derived-evidence |
| assurance-summary | artifacts/assurance/high-risk-escalation-demo/assurance-summary.json | tenant-isolation-waiver-has-reviewable-metadata | status=warning; missingLanes=spec, runtime; missingEvidenceKinds=runtime-control, waiver; warnings=insufficient-independent-lanes, missing-spec-derived-evidence |
| claim-evidence-manifest | artifacts/assurance/high-risk-escalation-demo/claim-evidence-manifest.json | tenant-isolation-enforced-before-account-read | status=partial; missingEvidenceRefs=missing-cross-tenant-property-evidence, missing-runtime-tenant-isolation-control |
| claim-evidence-manifest | artifacts/assurance/high-risk-escalation-demo/claim-evidence-manifest.json | tenant-isolation-waiver-has-reviewable-metadata | status=waived; missingEvidenceRefs=missing-waiver-owner-reason-expiry |

## Waivers / runtime controls

Waived and runtime-mitigated claims require explicit reviewer attention; they are not counted as satisfied proof.

| claim | waiver/control | status | owner | expires | source |
| --- | --- | --- | --- | --- | --- |
| tenant-isolation-waiver-has-reviewable-metadata | waiver-tenant-isolation-rollout-window-001 | active | not provided | not provided | artifacts/assurance/high-risk-escalation-demo/claim-evidence-manifest.json |
| tenant-isolation-waiver-has-reviewable-metadata | waiver-tenant-isolation-rollout-window-001 | active | not provided | not provided | claim-evidence-manifest |

## Policy decision / report-only vs blocking

| artifact | risk label | assurance mode | assurance result | ok | errors | warnings |
| --- | --- | --- | --- | --- | --- | --- |
| artifacts/policy/high-risk-escalation-demo/policy-gate-summary.high-risk.json | risk:high | strict | block | false | 9 | 0 |

## Reviewer action list

- Start with this Markdown before raw logs; then open `artifacts/assurance/high-risk-escalation-demo/assurance-summary.json` and `artifacts/policy/high-risk-escalation-demo/policy-gate-summary.high-risk.json`.
- Treat producer assertions as evidence input only; do not treat producer conclusion as approval.
- Follow recommendedReviewerAction=`review-unresolved-claims`: Assurance warning claims=2, unresolved/partial manifest claims=1, claims with missing evidence=2.
- Resolve or explicitly accept the listed missing evidence / unresolved claim rows before using the surface as release evidence.
- Boundary artifact is missing or not provided; record why scope drift is not assessed, or generate the Boundary Map summary.
- For ordinary PRs, report-only findings remain reviewer context; for risk/high-assurance PRs, follow policy decision result=`block` mode=`strict`.

## Interpretation guardrails

- Producer conclusion is not approval.
- Green baseline checks are not proof for high-assurance claims.
- Missing optional artifacts must stay visible as `missing` / `not provided`.
- Policy escalation depends on risk labels, assurance profile, and selected critical claims, not on the agent vendor.
