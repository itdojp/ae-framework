# Mock / Fixture Strategy (Test Stability Phase 3)

## Goal
- Reduce flakiness by making tests deterministic and hermetic.
- Make failures reproducible with explicit inputs and timestamps.

## Assumptions (versions)
- Node.js >=20.11 <23 (see `package.json` engines)
- pnpm 10.x (see `package.json` packageManager)
- Vitest 2.x (see `package.json` devDependencies)
- Deterministic seed is read from `AE_SEED` (`src/core/seed.ts`)

## Standard fixture locations
- `tests/fixtures/` for test-only fixtures
- `fixtures/` for shared fixtures across tools
- `test-cassettes/` for recorded inputs/outputs
- `artifacts/` for generated outputs used by follow-up steps

## Core principles
1. No external network calls in tests; use local fixtures/cassettes.
2. Freeze or inject time and randomness.
3. Explicit cleanup of temp files and environment variables.

## Recommended patterns

### Time
- Use `vi.useFakeTimers()` and `vi.setSystemTime(...)`.
- Restore timers in `afterEach` to avoid cross-test leakage.

### Randomness
- Use `AE_SEED` with deterministic generators (`src/core/seed.ts`, `src/codegen/deterministic-generator.ts`).
- For randomized test order, reuse `tests/utils/test-randomizer.ts`.
- Avoid direct `Math.random()` in tests; wrap and inject.

### IO / File system
- Use temp directories under `tmp/` or `test-cassettes/`.
- Ensure files are removed in teardown hooks.
- Keep `TZ=UTC` for deterministic timestamps when relevant.

### Network / External services
- Record responses into `test-cassettes/` and replay in tests.
- Prefer local stubs for CLI tests (JSON fixtures under `fixtures/`).

## Review checklist
- Deterministic input data is present in `fixtures/` or `test-cassettes/`.
- Randomness uses a seed (`AE_SEED`) or deterministic generator.
- Time is frozen when the test depends on clocks.
- No outbound network calls.
- Cleanup is explicit (files, env vars, timers).

## Tooling
- `pnpm run hermetic:quick` for non-determinism checks.
- `pnpm run test:fast` for a quick local verification.

## Related
- `docs/testing/flaky-test-triage.md`
- `docs/testing/replay-runner.md`
- `docs/testing/test-categorization.md`
