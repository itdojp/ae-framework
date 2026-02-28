# Branch Cleanup Report (2026-02-28)

## Scope

- Issue: #2321
- Repository: `itdojp/ae-framework`
- Cleanup mode in this report: local safe-delete batch (`git branch -d`)

## Executed commands

```bash
pnpm run maintenance:branch:inventory
node scripts/maintenance/branch-cleanup.mjs --scope both --max 50   # dry-run
pnpm run maintenance:branch:cleanup:apply:local
pnpm run maintenance:branch:inventory
```

## Result summary

- Before cleanup (inventory):
  - local branches: 735
  - local merged safe-delete candidates: 39
- Apply result:
  - local deleted: 37
  - local failed: 2
- After cleanup (inventory):
  - local branches: 698
  - local merged safe-delete candidates: 2

## Failed branches and reasons

1. `feat/2292-agents-runbooks`
   - reason: merged to `HEAD` but not fully merged to upstream tracking branch (`origin/feat/2292-agents-runbooks`) according to `git branch -d`.
2. `fix/codeql-unused-vars-cli`
   - reason: branch is currently used by linked worktree:
     `/home/devuser/work/CodeX/ae-frameworkA/ae-framework-unused-vars-cli`

## Operational updates applied

- Repository setting updated:
  - `delete_branch_on_merge=true`
  - `allow_auto_merge=true` (already enabled and confirmed)

## Next steps

- Remote merged branches are still numerous (current inventory candidate count: 260).
- Execute remote cleanup in controlled batches after review/approval:
  - `node scripts/maintenance/branch-cleanup.mjs --scope remote --max 100 --apply`
