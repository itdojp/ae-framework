# Progress Summary (artifacts/progress/summary.json)

Progress summary aggregates the latest progress, quality, and traceability signals into a single JSON file.

## Generate

```bash
node scripts/progress/aggregate-progress.mjs
# or
pnpm run progress:summary
```

## Inputs (defaults)

- `metrics/project-metrics.json`
- `reports/quality-gates/quality-report-*-latest.json`
- `traceability.json`
- `.ae/phase-state.json`

## Output

- `artifacts/progress/summary.json`

## Environment overrides

- `PROGRESS_METRICS`
- `PROGRESS_QUALITY`
- `PROGRESS_TRACEABILITY`
- `PROGRESS_PHASE_STATE`
- `PROGRESS_SUMMARY_OUTPUT`

## Output shape (high level)

- `generatedAt`
- `sources` (resolved file paths)
- `progress` (phase state summary)
- `metrics` (TDD/coverage totals)
- `quality` (gate summary)
- `traceability` (link coverage)
- `missing` (unavailable sources)
