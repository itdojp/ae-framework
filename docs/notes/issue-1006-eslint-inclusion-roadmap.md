# Issue 1006: ESLint Inclusion Roadmap

## Snapshot
- Date: 2026-01-24
- Scope: `configs/eslint.config.js` ignore list re-enable plan

## Background
Verify Lite stability required temporary exclusions in ESLint. This roadmap
phases the directories back in with measurable criteria to keep CI green.

## Current temporary exclusions
From `configs/eslint.config.js`:
- `src/ui/**`
- `src/agents/**`
- `src/cli/**`
- `src/commands/**`
- `src/services/**`
- `src/api/**`
- `src/benchmark/**`

## Proposed milestones (dates are targets)

### Phase 1 (by 2026-02-15)
Re-enable smaller core surfaces with lower dependency spread.
- `src/commands/**`
- `src/services/**`

Criteria:
- Verify Lite lint diff <= +50 new warnings
- No new `ts-expect-error` without description

### Phase 2 (by 2026-03-15)
Re-enable user-facing CLI logic and API surface.
- `src/cli/**`
- `src/api/**`

Criteria:
- Verify Lite lint diff <= +50 new warnings
- Type-coverage stays >= current baseline

### Phase 3 (by 2026-04-15)
Re-enable agent orchestrations and benchmarking.
- `src/agents/**`
- `src/benchmark/**`

Criteria:
- No new error-level rules
- Lint summary is stable for 2 consecutive PRs

### Phase 4 (by 2026-05-15)
Re-enable UI last due to accessibility and JSX rule surface.
- `src/ui/**`

Criteria:
- a11y checks remain green
- UI lint warnings are triaged with owners

## Execution notes
- Each phase should land as a small PR with a clear lint delta summary.
- If the delta is large, split by subdirectory and update the baseline.
