# Issue 1005: Integration Test Inventory (Phase 1)

## Snapshot
- Commit: 61f30b60
- Integration project files: 5

## Files and helper usage
| file | temp dir | cleanup | retry | integration setup |
| --- | --- | --- | --- | --- |
| tests/integration/integration-cli.test.ts | yes | no | yes | no |
| tests/integration/system-validation.test.ts | yes | yes | yes | no |
| tests/integration/test-orchestrator.test.ts | yes | yes | yes | no |
| tests/integration/web-api/reservations.test.ts | no | no | yes | no |
| tests/optimization/system-integration.test.ts | no | yes | no | yes |

## Notes
- This inventory is a baseline for flake investigation and cleanup planning.
- If a file shows "no" across cleanup helpers, review its teardown behavior first.