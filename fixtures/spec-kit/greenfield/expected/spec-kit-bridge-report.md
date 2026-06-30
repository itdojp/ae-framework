# Spec Kit Bridge Report: Reservation Approval

- Result: `pass`
- Generated at: 2026-06-30T00:00:00.000Z
- Feature directory: `fixtures/spec-kit/greenfield/specs/001-reservation-approval`
- Upstream: https://github.com/github/spec-kit (main)

## Summary

- Requirements: 3
- User stories: 2
- Tasks: 8
- Contracts: 1
- Findings: 0
- Ambiguous mappings: 6
- Lossy mappings: 6

## Outputs

- bridge-report: `fixtures/spec-kit/greenfield/expected/spec-kit-bridge-report.json` (schema/spec-kit-bridge-report.schema.json)
- context-pack: `fixtures/spec-kit/greenfield/expected/context-pack.import.json` (schema/context-pack-v1.schema.json)
- exec-plan: `fixtures/spec-kit/greenfield/expected/exec-plan.v2.json` (schema/exec-plan.v2.schema.json)

## Findings

- None.

## Mapping highlights

- spec.requirement `FR-001` -> context-pack.acceptance-test `AT-FR-001` (high)
- spec.requirement `FR-002` -> context-pack.acceptance-test `AT-FR-002` (high)
- spec.requirement `FR-003` -> context-pack.acceptance-test `AT-FR-003` (high)
- spec.user-story `US1` -> context-pack.morphism `ReservationApproval.US1` (medium)
- spec.user-story `US2` -> context-pack.morphism `ReservationApproval.US2` (medium)
- tasks.task `T001` -> exec-plan.taskGraph.node `task.t001` (medium, lossy)
- tasks.task `T002` -> exec-plan.taskGraph.node `task.t002` (medium, lossy)
- tasks.task `T003` -> exec-plan.taskGraph.node `task.t003` (medium, lossy)
- tasks.task `T004` -> exec-plan.taskGraph.node `task.t004` (high)
- tasks.task `T005` -> exec-plan.taskGraph.node `task.t005` (high)
- tasks.task `T006` -> exec-plan.taskGraph.node `task.t006` (high)
- tasks.task `T007` -> exec-plan.taskGraph.node `task.t007` (high)
- tasks.task `T008` -> exec-plan.taskGraph.node `task.t008` (medium, lossy)
- contracts.file `reservation-api.openapi.yaml` -> exec-plan.context.specKitRefs `contract.reservation-api-openapi` (high)

## Unsupported / lossy fields

- spec-kit-command agent hooks and invocation side effects: ae-framework bridge records artifact references but does not execute Spec Kit commands, agent hooks, or task-to-issues side effects. (report-only-lossy)
- tasks free-form task prose ordering: Tasks are mapped to ExecPlan nodes and Context Pack references; nuanced prose ordering remains in the source task line. (preserved-as-source-reference)
