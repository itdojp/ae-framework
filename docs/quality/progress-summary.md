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

Note: Phase state resolution checks `PROGRESS_PHASE_STATE` first, then falls back to `AE_PHASE_STATE_FILE` when set. If neither is provided, `AE_PHASE_STATE_ROOT` is honored (using `<root>/.ae/phase-state.json`) before falling back to `.ae/phase-state.json` in the current working directory.

## Output shape (high level)

- `generatedAt`
- `sources` (resolved file paths)
- `progress` (phase state summary)
- `metrics` (TDD/coverage totals)
- `quality` (gate summary)
- `traceability` (link coverage)
- `missing` (unavailable sources)
