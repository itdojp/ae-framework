# CI / test runner fixture

Raw fixture: `test-runner-output.json`

## Producer boundary

CI logs, coverage summaries, and check conclusions are producer output. They support scoped evidence only after path, head SHA, and schema-backed summary validation.

## Expected normalized routing

- `verify-lite-run-summary` for required-check and command status.
- `quality-scorecard` / `report-envelope` for coverage and quality-gate evidence.
- `producer-normalization-summary/v1` for report-only routing of raw CI signals.
- `claim-evidence-manifest/v1` for tested claims, while keeping test evidence separate from proof.
- `hook-feedback/v1` when failed, stale, or missing checks must be returned to a producer.

Green checks do not prove high-assurance claims outside their command scope.
