# Stable CI Test Profile

This profile provides deterministic, faster test execution suitable for PR verification. Heavy or flaky suites are gated behind labels or nightly jobs.

## Commands
- Full CI config: `pnpm run test:ci`
- Stable subset: `pnpm run test:ci:stable`

`test:ci:stable` currently excludes:
- `**/system-integration.test.ts`

## Usage in Workflows
- For PR workflows aiming for reliability and speed, run `test:ci:stable` or target explicit suites (`test:unit`, `test:int`, `test:a11y`, `test:coverage`).
- Keep Playwright/E2E runs label-gated (`run-e2e`) or scheduled/nightly.

## Evolution
- As we identify more flaky suites, we will either stabilize them (preferred) or move them to label/nightly until fixed.

