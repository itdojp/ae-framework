# Issue 1005: Integration Test Inventory (Phase 1)

## Snapshot
- Commit: b44585eb
- Integration project files: 5

## Files and helper usage
| file | temp dir | cleanup | retry | integration setup |
| --- | --- | --- | --- | --- |
| tests/integration/integration-cli.test.ts | yes | yes (temp dir) | yes | yes |
| tests/integration/system-validation.test.ts | yes | yes | yes | yes |
| tests/integration/test-orchestrator.test.ts | yes | yes | yes | yes |
| tests/integration/web-api/reservations.test.ts | no | yes | yes | yes |
| tests/optimization/system-integration.test.ts | no | yes | yes | yes |

## Notes
- This inventory is a baseline for flake investigation and cleanup planning.
- `createIntegrationTempDir` registers cleanup automatically; the cleanup column treats that as covered.
- If a file shows "no" across cleanup helpers, review its teardown behavior first.
