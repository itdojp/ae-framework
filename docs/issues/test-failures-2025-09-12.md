# Test Failures Tracking – 2025-09-12

Status
- TypeScript types: clean (`pnpm types:check` passes)
- Build: passes (`pnpm build`)
- Fast tests: failing (behavioral issues not related to types)

Summary of failing areas
- Resilience / Timeout Patterns
  - TimeoutWrapper/AdaptiveTimeout behavior causing failures
  - Errors observed: 
    - expected error to be instance of TimeoutError
    - Cannot access 'timeoutPromise' before initialization
  - Circuit Breaker expectations in backoff tests (state OPEN timing) and unhandled rejections from simulated HTTP failures
- Test Randomizer
  - TypeError: Cannot read properties of undefined (reading 'id') at `tests/utils/test-randomizer.ts:172`

Repro
```bash
pnpm test:fast
```

Details
- Timeout Patterns
  - `TimeoutWrapper` uses a Promise (`timeoutPromise`) with a self-stored `timeoutId` on the promise object. Tests show TDZ-like issue: “Cannot access 'timeoutPromise' before initialization”.
  - `AdaptiveTimeout` relies on `TimeoutWrapper`; tests expecting TimeoutError instances and onTimeout callback calls are failing.
- Backoff/Circuit Breaker
  - Unhandled rejections from `ResilientHttpClient.executeHttpRequest` during tests that simulate `HTTP 500` responses.
  - Tests expect Circuit Breaker to transition to OPEN; state transition timing may need adjustment or test harness should await properly.
- Test Randomizer
  - Fails when reading `.id` on undefined; indicates input generation/shuffle path produces undefined entries without guards.

Scope (proposed)
- Timeout Patterns
  - Refactor `TimeoutWrapper.execute` to store timeout id in a local variable instead of attaching to the promise; clear it in a finally block to avoid TDZ/self-reference.
  - Verify `onTimeout` and `AbortController` paths; ensure thrown error is a `TimeoutError` instance.
- Circuit Breaker / Backoff
  - Add test-safe hooks or awaitable transitions, or adjust delay/threshold logic to meet test timing expectations.
  - Catch and assert on rejections within tests to avoid unhandled rejections in runner.
- Test Randomizer
  - Add input validation and guards where the execution list is built and logged (avoid undefined entries, or filter them out).

Acceptance Criteria
- `pnpm test:fast` passes locally with no unhandled errors and all previously failing suites green:
  - `tests/resilience/timeout-patterns.test.ts`
  - `tests/resilience/backoff-strategies.test.ts`
  - `tests/utils/test-randomizer.spec.ts`
- No regressions introduced in type checks or build.

Notes
- This issue is split from the types/build stabilization task to keep scope focused. Behavioral fixes can be iterative with targeted PRs per subsystem (Timeouts, Backoff/Circuit, Randomizer).

