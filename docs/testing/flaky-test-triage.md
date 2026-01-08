# Flaky Test Triage (CI)

Purpose: Provide a minimal, repeatable checklist to diagnose flaky tests without expanding CI cost.

## 1) Capture signal
- Link the failing CI run and job
- Note the exact test name and file
- Record the command used in CI (from logs)

## 2) Reproduce locally
- Run the closest local equivalent:
  - `pnpm run test:ci:lite`
  - or the specific suite (unit/integration/property/mbt)
- If Vitest stalls, try:
  - `vitest --run --reporter=verbose --maxWorkers=50% --bail`

## 3) Isolate the test
- Use a name or file filter to limit scope
- Run the test multiple times (3-5) to confirm flakiness
- Check for shared state, timers, or network dependency

## 4) Classify the cause
- **Environment**: filesystem, ports, timeouts, CI resources
- **Data**: nondeterministic inputs, time-based values
- **Concurrency**: race conditions, shared globals
- **External**: network calls, external services

## 5) Mitigate safely
- Add deterministic fixtures or mocks
- Add explicit timeouts and cleanup
- Gate heavy tests with labels (`docs/ci/label-gating.md`)
- Prefer stable profile (`docs/ci/stable-profile.md`) for baseline

## 6) Document outcome
- Add a short note in the PR or issue:
  - What failed, why, and how it was fixed
  - Whether a new guard/gate is required

## References
- `docs/testing/test-categorization.md`
- `docs/testing/parallel-execution-strategy.md`
- `docs/ci/label-gating.md`
- `docs/ci/stable-profile.md`
