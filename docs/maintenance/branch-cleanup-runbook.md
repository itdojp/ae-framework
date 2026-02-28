# Branch Cleanup Runbook

This runbook defines a safe, repeatable process for branch cleanup.

## Scope

- Target repository: `ae-framework`
- Goal: reduce stale branch noise without deleting protected or unmerged work
- Safe default: **merged branches only**

## Protected branch rules

The cleanup scripts never delete branches that match:

- Exact names: `main`, `master`, `develop`, `staging`
- Prefixes: `release/`, `hotfix/`

## Commands

### 1) Inventory (always first)

```bash
pnpm run maintenance:branch:inventory
```

Outputs:

- `tmp/maintenance/branch-inventory.json`
- `tmp/maintenance/branch-inventory.md`

### 2) Dry-run cleanup candidates

```bash
pnpm run maintenance:branch:cleanup:dry-run
```

This prints planned delete commands and writes:

- `tmp/maintenance/branch-cleanup-report.json`

### 3) Apply first safe batch (local only)

```bash
pnpm run maintenance:branch:cleanup:apply:local
```

Notes:

- Uses `git branch -d` (safe delete; refuses unmerged branches)
- Batch size default: 200 branches
- Repeat in batches until target count is reached

## Remote branch cleanup policy

Remote deletion is not executed by default in automation scripts.
Use remote deletion only after:

1. inventory report review,
2. confirmation that branches are merged,
3. explicit operator approval.

When approved, run:

```bash
node scripts/maintenance/branch-cleanup.mjs --scope remote --max 100 --apply
```

## Operational checklist

- [ ] Inventory generated and reviewed
- [ ] Dry-run output archived
- [ ] Safe local cleanup executed in batches
- [ ] Remote cleanup approved and executed (if needed)
- [ ] Cleanup result summary added to issue/PR comment

## Recommended cadence

- Weekly: inventory + local safe cleanup
- Monthly: remote merged cleanup with approval
