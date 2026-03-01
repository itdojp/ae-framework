# TODO Triage Backlog (2026-03-01)

Issue: #2359 (refreshed after #2333 close)

## Snapshot
- Markers triaged: 19
- now: 0
- planned: 14
- drop: 5

## Reduction
- 2026-02-28 snapshot: 75 markers
- 2026-03-01 snapshot: 19 markers
- reduced: 56 markers (74.7%)

## Immediate backlog (`triage_status=now`)
- none

## Planned backlog by area (`triage_status=planned`)
- src: 11
- api: 2
- scripts: 1

## Dropped marker groups (`triage_status=drop`)
- `tests/unit/scripts/extract-todo-markers.test.ts`: 3 markers
- `docs/maintenance/todo-triage-runbook.md`: 1 markers
- `tests/unit/docs/check-doc-todo-markers.test.ts`: 1 markers

## Next actions
- planned 項目を area 別（src/api/scripts）で分割して個別Issue化する。
- `scripts/hooks/pre-commit` の marker policy TODO を先行実装候補として扱う。
