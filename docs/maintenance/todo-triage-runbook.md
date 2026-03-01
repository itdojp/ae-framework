# TODO/FIXME/XXX Triage Runbook

This runbook defines how to inventory and triage TODO markers into actionable backlog items.

## Objective

- Convert scattered TODO markers into a prioritized, traceable backlog.
- Remove obsolete markers and keep valid markers auditable.

## Inventory command

```bash
pnpm run maintenance:todo:extract
```

Default outputs:

- `tmp/maintenance/todo-markers.csv`
- `tmp/maintenance/todo-markers-summary.md`

For issue tracking snapshots, copy the triaged `todo-markers.csv` (and optionally
the generated `todo-markers-summary.md`) into dated docs under `docs/maintenance/`,
add a separate curated backlog snapshot markdown file, and include links in
`docs/README.md`.

## Triage dimensions

Each row should be evaluated on these columns:

- `triage_status`:
  - `now` (immediate action)
  - `planned` (scheduled work)
  - `drop` (obsolete/invalid marker)
- `severity`:
  - `S1` critical
  - `S2` high
  - `S3` medium
  - `S4` low
- `impact`:
  - `runtime`
  - `quality`
  - `security`
  - `devex`
  - `docs`
- `reproducibility`:
  - `deterministic`
  - `intermittent`
  - `unknown`
- `dependency`:
  - `none`
  - `internal`
  - `external`

## Prioritization rule (recommended)

Escalate to individual issue when:

1. `triage_status=now`, or
2. `severity` is `S1/S2`, or
3. `impact=security`, or
4. marker has no issue reference and affects `src/`, `scripts/`, or `.github/workflows/`.

## Hygiene rules

- New TODO markers should include issue references when possible (for example `TODO(#<issue>): ...`).
- Remove markers with `triage_status=drop` in the same PR whenever safe.
- Avoid large mixed PRs; separate “inventory/triage” and “implementation/removal”.
- Keep `triage_status=now` items linked to dedicated issues and record them in
  a dated backlog snapshot.
- For scaffolds/examples, prefer neutral placeholders such as `NEXT:` or
  `IMPLEMENT:` instead of `TODO:` to avoid backlog noise.
