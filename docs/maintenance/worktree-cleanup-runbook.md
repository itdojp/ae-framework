# Worktree Cleanup Runbook

This runbook defines a safe process to remove stale local worktrees that are already merged.

## Scope

- Target repository: `ae-framework`
- Goal: reduce stale worktree noise and avoid merge/conflict overhead
- Safe default: **only branch-attached worktrees whose branch is already merged to base**

## Protected branch rules

The cleanup script never removes worktrees attached to:

- Exact names: `main`, `master`, `develop`, `staging`
- Prefixes: `release/`, `hotfix/`

## Commands

### 1) Dry-run (recommended first)

```bash
pnpm run maintenance:worktree:cleanup:dry-run
```

This runs `git worktree prune` before analysis and writes:

- `tmp/maintenance/worktree-cleanup-report.json`

### 2) Apply safe cleanup batch

```bash
pnpm run maintenance:worktree:cleanup:apply
```

Notes:

- Uses `git worktree remove` (fails for dirty worktrees; no force-delete)
- Batch size default: 50 worktrees
- Repeat in batches if required

## Manual fallback commands

```bash
# List detailed worktree state
git worktree list --porcelain

# Run with custom base and larger batch
node scripts/maintenance/worktree-cleanup.mjs --base origin/main --max 100 --prune --apply
```

## Operational checklist

- [ ] Dry-run report generated and reviewed
- [ ] Branch protection rules confirmed
- [ ] Apply run executed
- [ ] Failed removals reviewed (dirty/locked/missing branch)
- [ ] Cleanup summary posted to issue/PR
