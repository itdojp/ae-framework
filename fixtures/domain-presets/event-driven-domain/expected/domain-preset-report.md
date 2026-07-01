# Domain Assurance Preset: Event-driven domain assurance preset

- presetId: `event-driven-domain`
- generatedAt: `2026-07-01T00:00:00.000Z`
- classification: `structured-assurance`
- reportOnly: `true`
- startingCommand: `pnpm run conformance:verify:sample`

## Target user

Teams maintaining inventory, ordering, payment, or workflow domains where replayable events and invariants are more important than a single HTTP request path.

## Recommended when

- Domain correctness depends on event ordering, replay, idempotency, or aggregate invariants.
- Reviewers can inspect sample event traces and rule definitions locally.
- The team wants conformance evidence before considering heavier formal lanes.

## Not recommended when

- The product has no retained event trace or deterministic replay fixture.
- The change is a UI-only copy update or a one-off migration with no domain invariant.
- The team cannot define expected event outcomes or conformance rules.

## Required inputs

| ID | Input | Path pattern | Contract |
| --- | --- | --- | --- |
| event-samples | Sample domain events | configs/samples/sample-data.json or examples/inventory/artifacts/domain/*.json | project-local event fixture |
| conformance-rules | Conformance rules | configs/samples/sample-rules.json | conformance rule set |
| context-pack | Context Pack and Boundary Map | spec/context-pack/**/*.{json,yaml,yml} | context-pack/v1 + context-pack-boundary-map/v1 |
| exec-plan | ExecPlan v2 | artifacts/plan/exec-plan.v2.json or fixtures/exec-plan/*.json | exec-plan/v2 |

## Verification commands

| ID | Command | Purpose |
| --- | --- | --- |
| context-pack-validate | `pnpm run context-pack:validate` | Validate the domain boundary and acceptance input before replay work. |
| conformance-sample | `pnpm run conformance:verify:sample` | Exercise the deterministic event/rule fixture. |
| verify-lite | `pnpm run verify:lite` | Keep the default PR-quality baseline alongside domain replay evidence. |

## Expected artifacts

| ID | Path | Required | Review purpose |
| --- | --- | --- | --- |
| conformance-result | artifacts/hermetic-reports/conformance/sample-results.json | yes | Shows invariant or rule failures over deterministic event samples. |
| conformance-summary | artifacts/hermetic-reports/conformance/summary.json | no | Aggregates conformance findings for PR or release review. |
| verify-lite-summary | artifacts/verify-lite/verify-lite-run-summary.json | yes | Shows whether the ordinary local verification lane passed. |
| assurance-summary | artifacts/assurance/assurance-summary.json | no | Connects conformance evidence to claim/evidence status when an assurance profile is present. |

## Escalation rule

- trigger: Escalate when replay is non-deterministic, an invariant fails, ordering assumptions are disputed, or the domain is payment/auth/safety critical.
- action: Add property/model/formal lanes and require a human decision on whether the invariant is blocking or report-only.
- human decision required: yes

## Reused contracts

- context-pack/v1
- context-pack-boundary-map/v1
- exec-plan/v2
- conformance-verify-result/v1
- conformance-report/v1
- assurance-summary/v1

## Boundaries

- Domain presets select inputs, commands, and evidence surfaces; they do not approve, merge, or change policy-gate enforcement.
- No live external APIs were called.
