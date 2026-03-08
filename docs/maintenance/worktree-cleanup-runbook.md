# Worktree Cleanup Runbook

This runbook defines a safe process to remove stale local worktrees that are already merged.

Related:

- Subagent isolation and lifecycle: `docs/maintenance/subagent-worktree-runbook.md`

## Scope

- Target repository: `ae-framework`
- Goal: reduce stale worktree noise and avoid merge/conflict overhead
- Safe default: **only branch-attached worktrees whose branch is already merged to base**
- detached worktree は自動削除しない。inventory の `detachedWorktreesOnBaseClean` で人手確認する

## Merge semantics note

- This tool defines "merged" as `git merge-base --is-ancestor <branch> <base>`.
- In squash-merge workflows, a merged PR branch may not be an ancestor of `base`,
  so it can still be reported as `branch-not-merged`.
- If squash-merged branches should be treated as merged, run with a custom
  `isMergedToBase` strategy (wrapper script / API-assisted check).

## Protected branch rules

The cleanup script never removes worktrees attached to:

- Exact names: `main`, `master`, `develop`, `staging`
- Prefixes: `release/`, `hotfix/`

補助的に `pnpm run maintenance:branch:inventory` を実行すると、次も確認できる:

- `linkedWorktreeBranches`: linked worktree で現在使用中の branch
- `detachedWorktreesOnBaseClean`: clean かつ `HEAD` が base に含まれる detached worktree

## Commands

### 1) Dry-run (recommended first)

```bash
pnpm run maintenance:worktree:cleanup:dry-run

# Refresh origin/* before comparing worktree branches to a remote-tracking base
node scripts/maintenance/worktree-cleanup.mjs --base origin/main --fetch
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
- detached worktree はこのコマンドでは削除対象に入らない
- `--fetch` は `--base` から remote 名を導出し、`git fetch --prune <remote>` を先に実行する

## Manual fallback commands

```bash
# List detailed worktree state
git worktree list --porcelain

# Inventory includes detached/manual-review candidates
pnpm run maintenance:branch:inventory

# Run with custom base and larger batch
node scripts/maintenance/worktree-cleanup.mjs --base origin/main --max 100 --prune --apply
```

## Operational checklist

- [ ] Dry-run report generated and reviewed
- [ ] Branch protection rules confirmed
- [ ] Apply run executed
- [ ] Failed removals reviewed (dirty/locked/missing branch)
- [ ] Cleanup summary posted to issue/PR
- [ ] Active subagent worktrees excluded or already integrated
- [ ] Detached/manual-review candidates reviewed separately
