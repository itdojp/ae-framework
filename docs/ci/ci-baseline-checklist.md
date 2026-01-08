# CI Baseline Checklist

Purpose: Provide a minimal checklist to confirm the CI baseline is healthy without running heavy suites.

## When to use
- After CI pipeline changes
- After dependency updates
- When flaky test volume increases

## Baseline checks (minimum)
- Verify Lite is green
- Lint/type/coverage steps pass
- Required gate jobs are green

## Commands
- `pnpm run verify:lite`
- `pnpm run test:ci:lite`

## CI notes
- Heavy suites are label-gated (see `docs/ci/label-gating.md`)
- Prefer stable profile for baseline signal (`docs/ci/stable-profile.md`)

## Failure triage
- Use `docs/testing/flaky-test-triage.md` for reproduction and isolation
- Refer to `docs/testing/test-categorization.md` to pick the right suite
- Keep a short log in `docs/notes/pipeline-baseline.md` when investigating
