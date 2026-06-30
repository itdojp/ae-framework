# Spec Kit Bridge Report: Inventory Modernization

- Result: `warning`
- Generated at: 2026-06-30T00:00:00.000Z
- Feature directory: `fixtures/spec-kit/brownfield/specs/042-inventory-modernization`
- Upstream: https://github.com/github/spec-kit (main)

## Summary

- Requirements: 2
- User stories: 1
- Tasks: 4
- Contracts: 0
- Findings: 2
- Ambiguous mappings: 4
- Lossy mappings: 5

## Outputs

- bridge-report: `fixtures/spec-kit/brownfield/expected/spec-kit-bridge-report.json` (schema/spec-kit-bridge-report.schema.json)
- context-pack: `fixtures/spec-kit/brownfield/expected/context-pack.import.json` (schema/context-pack-v1.schema.json)
- exec-plan: `fixtures/spec-kit/brownfield/expected/exec-plan.v2.json` (schema/exec-plan.v2.schema.json)

## Findings

- [warning] missing-contracts: No contracts/* files were found; contract mappings are recorded as not_collected. (fixtures/spec-kit/brownfield/specs/042-inventory-modernization/contracts)
- [warning] ambiguous-task-story: T004 has no [US#] marker; it is preserved as an ExecPlan task but cannot be linked to a specific user story. (fixtures/spec-kit/brownfield/specs/042-inventory-modernization/tasks.md)

## Mapping highlights

- spec.requirement `FR-001` -> context-pack.acceptance-test `AT-FR-001` (high)
- spec.requirement `FR-002` -> context-pack.acceptance-test `AT-FR-002` (high)
- spec.user-story `US1` -> context-pack.morphism `InventoryModernization.US1` (medium)
- tasks.task `T001` -> exec-plan.taskGraph.node `task.t001` (medium, lossy)
- tasks.task `T002` -> exec-plan.taskGraph.node `task.t002` (medium, lossy)
- tasks.task `T003` -> exec-plan.taskGraph.node `task.t003` (high)
- tasks.task `T004` -> exec-plan.taskGraph.node `task.t004` (medium, lossy)

## Unsupported / lossy fields

- spec-kit-command agent hooks and invocation side effects: ae-framework bridge records artifact references but does not execute Spec Kit commands, agent hooks, or task-to-issues side effects. (report-only-lossy)
- tasks free-form task prose ordering: Tasks are mapped to ExecPlan nodes and Context Pack references; nuanced prose ordering remains in the source task line. (preserved-as-source-reference)
