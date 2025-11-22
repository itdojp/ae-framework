# ExecPlan: Web API / 04-verify

## Goal
- Run mandatory quality gates, produce artifacts, and compare heavy-test trends if available.

## Mandatory checks
- Lint, type-check
- Unit + integration (HTTP)
- Property tests (seeded)

## Optional (time-boxed)
- Mutation quick: `STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick`
- MBT/property long-run if cache available

## Steps
1) `pnpm run lint && pnpm run test:fast`
2) `pnpm run test:integration -- --runInBand` (or equivalent script)
3) `pnpm run test:property -- --runInBand --maxWorkers=50%`
4) If heavy cache present: `node scripts/pipelines/sync-test-results.mjs --restore`
5) Compare trends: `node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json`
6) Snapshot cache (if updated): `node scripts/pipelines/sync-test-results.mjs --store --snapshot`
7) Attach summary to PR (or upload artifact)
