---
docRole: ssot
lastVerified: 2026-03-11
owner: testing-docs
verificationCommand: pnpm -s run check:doc-consistency
---
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
- Follow `docs/testing/mock-fixture-strategy.md` for baseline patterns
- Add explicit timeouts and cleanup
- Gate heavy tests with labels (`docs/ci/label-gating.md`)
- Prefer stable profile (`docs/ci/stable-profile.md`) for baseline

## 6) Document outcome
- Add a short note in the PR or issue:
  - What failed, why, and how it was fixed
  - Whether a new guard/gate is required

## Enhanced detector execution budget

The quick lane runs the unchanged `test:fast` suite three times
(`--runs 3 --threshold 0.15`). Each attempt has a 240-second execution deadline,
a 2-second termination grace period and a 1-second pipe-drain bound. The matrix
step allows 15 minutes, including reporting margin. A successful hosted suite
took 161.56 seconds; the former 90-second wrapper deadline could terminate
otherwise passing suites. Do not reduce run count, exclude tests or raise the
failure threshold to make this lane green.

On POSIX runners the detector terminates its owned process group, not just the
package-manager wrapper. Descendants that create a new process group are outside
that cleanup guarantee; pipe waiting is still bounded. Windows uses direct-child
termination, not a process-tree guarantee.

Timeout remains failed execution with `status=timeout`, `timedOut=true`,
observed exit/signal/duration and the configured deadline in the report. Missing
commands are `tool-error`; nonzero test results remain failures. Explicit
outcomes outrank keyword-based classifications. Reports are written before a
threshold failure produces a nonzero CLI exit.

The detector retains only the last 64 Ki characters per output stream in memory;
raw output is not added to the uploaded summary. Inspect the corresponding
CI Fast log for assertion details; absent output is not success evidence.

## References
- `docs/testing/test-categorization.md`
- `docs/testing/parallel-execution-strategy.md`
- `docs/testing/mock-fixture-strategy.md`
- `docs/ci/label-gating.md`
- `docs/ci/stable-profile.md`
