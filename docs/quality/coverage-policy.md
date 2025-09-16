# Coverage Policy — Proposal and Operations

Goals
- Keep PRs fast and non-blocking by default; gate only on explicit signals
- Allow main branch to enforce thresholds via repository variables

Mechanics
- Threshold source order:
  1. PR label `coverage:<pct>` (e.g., `coverage:75`)
  2. Repository variable `COVERAGE_DEFAULT_THRESHOLD` (default 80)
- Enforcement (blocking) when:
  - PR has label `enforce-coverage`, or
  - Push to `main` and repository variable `COVERAGE_ENFORCE_MAIN` = `1`
- Reporting:
  - The `coverage-check` workflow posts a non-blocking PR comment with computed coverage and policy state

Recommended operations
- On PRs: use `/coverage <pct>` for ad-hoc thresholds and `/enforce-coverage` when you want blocking
- On `main`: set `COVERAGE_ENFORCE_MAIN=1` and `COVERAGE_DEFAULT_THRESHOLD` in repository variables

References
- Workflow: `.github/workflows/coverage-check.yml`
- Slash commands: see `AGENTS.md` and `docs/ci-policy.md`

