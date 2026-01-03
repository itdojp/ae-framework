# Issue #1225: Code Scanning Open Alerts Snapshot (2026-01-03)

This note captures the current GitHub code-scanning open alerts so we can triage and prioritize fixes.

## Summary

- Total open alerts: **193**
- Severity breakdown:
  - note: **144**
  - warning: **49**

## Rule breakdown

| Rule | Severity | Count | Notes |
| --- | --- | --- | --- |
| `js/unused-local-variable` | note | 144 | |
| `js/file-system-race` | warning | 15 | |
| `js/shell-command-injection-from-environment` | warning | 15 | |
| `js/file-access-to-http` | warning | 7 | |
| `js/useless-assignment-to-local` | warning | 5 | |
| `js/http-to-file-access` | warning | 2 | |
| `js/incomplete-sanitization` | warning | 2 | |
| `js/indirect-command-line-injection` | warning | 2 | |
| `js/insecure-randomness` | warning | 1 | |

## Top-level path distribution

| Path prefix | Count |
| --- | --- |
| `src/` | 88 |
| `scripts/` | 61 |
| `examples/` | 34 |
| `apps/` | 4 |
| `tests/` | 3 |
| `artifacts/` | 2 |
| `packages/` | 1 |

## Suggested triage focus

1. **Warnings first**: resolve or justify the 49 warning-level alerts.
2. **Separate generated or sample code**: determine if `js/unused-local-variable` in `examples/` or generated assets should be excluded or fixed.
3. **Narrow scope**: prioritize `src/` and `scripts/` where runtime risk is higher.

