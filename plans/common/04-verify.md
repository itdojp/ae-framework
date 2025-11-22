# ExecPlan: Common / 04-verify

## Goal
- Run mandatory quality gates and optional heavy tests; capture artifacts.

## Mandatory
- lint, type-check
- unit, integration
- property (seeded)

## Optional
- mutation quick (time-boxed)
- heavy cache restore/compare if available

## Steps (example)
1) `pnpm run lint && pnpm run test:fast`
2) `pnpm run test:integration -- --runInBand` (or project-specific)
3) `pnpm run test:property:webapi -- --runInBand --maxWorkers=50%` (adjust target)
4) If cache available: `node scripts/pipelines/sync-test-results.mjs --restore`
5) Compare trends: `node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json`
6) Snapshot cache: `node scripts/pipelines/sync-test-results.mjs --store --snapshot`
