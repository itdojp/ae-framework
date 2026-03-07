# Branch Cleanup Runbook

This runbook defines a safe, repeatable process for branch cleanup.
For stale worktree cleanup, use `docs/maintenance/worktree-cleanup-runbook.md`.
For remote branch review and approval flow, use `docs/maintenance/remote-branch-triage-runbook.md`.

## Scope

- Target repository: `ae-framework`
- Goal: reduce stale branch noise without deleting protected or unmerged work
- Safe default: **merged branches only**
- `scripts/maintenance/branch-cleanup.mjs` が自動削除するのは、Git ancestry 上 `base` に取り込まれた branch のみ
- GitHub 上で MERGED 済みでも ancestry で拾えない branch は、inventory では **manual review** として報告し、自動削除しない

## Protected branch rules

The cleanup scripts never delete branches that match:

- Exact names: `main`, `master`, `develop`, `staging`
- Prefixes: `release/`, `hotfix/`

## Commands

### 1) Inventory (always first)

```bash
pnpm run maintenance:branch:inventory

# Large repo or non-standard base
node scripts/maintenance/branch-inventory.mjs --base origin/main --gh-pr-limit 2000

# Render operator worksheet for remote cleanup
pnpm run maintenance:branch:triage:render

# Render Batch A/B/C review packs from the worksheet
pnpm run maintenance:branch:triage:batches

# Audit active issue / automation references before any remote delete decision
pnpm run maintenance:branch:triage:reference-audit
```

Outputs:

- `tmp/maintenance/branch-inventory.json`
- `tmp/maintenance/branch-inventory.md`

Inventory では次も併せて確認する:

- `localPrMergedManualReview`: GitHub 上では MERGED 済みだが ancestry では safe-delete 扱いにしない local branch
- `linkedWorktreeBranches`: linked worktree で使用中のため cleanup 対象から除外する branch
- `detachedWorktreesOnBaseClean`: `HEAD` が base 上にあり clean な detached worktree

`localPrMergedManualReview` は `gh` CLI で merged PR 情報を取得できる環境でのみ出力される。
必要に応じて `--gh-pr-limit` で取得件数を増やし、`--gh-pr-base` で GitHub 側の base branch 名を明示できる。

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
- `localPrMergedManualReview` に出た branch は、このコマンドでは削除されない

## Remote branch cleanup policy

Remote deletion is not executed by default in automation scripts.
Use remote deletion only after:

1. inventory report review,
2. triage worksheet review,
3. confirmation that branches are merged,
4. explicit operator approval.

The preferred path is to bind the delete scope to reviewed worksheet rows by using
`tmp/maintenance/remote-branch-triage.json` or an explicit approved branch list.
This avoids recomputing a wider batch at apply time.

When approved, run:

```bash
# Merged remote branches reviewed from the worksheet
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-manifest-json tmp/maintenance/remote-branch-triage.json \
  --remote-manifest-mode merged \
  --max 100 \
  --apply

# Reviewed stale branches whose worksheet rows were marked decision=delete
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-manifest-json tmp/maintenance/remote-branch-triage.json \
  --remote-manifest-mode stale-delete \
  --max 100 \
  --apply

# Explicit operator-approved subset (one branch per line, or JSON array)
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-branches-file tmp/maintenance/approved-remote-branches.txt \
  --max 100 \
  --apply
```

Safeguards:

- `triage-merged` keeps the ancestry check and blocks branches no longer merged to `base`
- triage manifest input must carry `sourceInventory.remote` and `sourceInventory.base`
- manifest rows with `branchOid` block deletion when the current remote tip no longer matches
- `--scope local` cannot be combined with reviewed remote inputs
- protected branches remain excluded even when explicitly listed

The operator workflow and worksheet format are defined in
`docs/maintenance/remote-branch-triage-runbook.md`.

## Operational checklist

- [ ] Inventory generated and reviewed
- [ ] `localPrMergedManualReview` / `linkedWorktreeBranches` / `detachedWorktreesOnBaseClean` を確認した
- [ ] Dry-run output archived
- [ ] Safe local cleanup executed in batches
- [ ] Remote cleanup approved and executed (if needed)
- [ ] Cleanup result summary added to issue/PR comment

## Recommended cadence

- Weekly: inventory + local safe cleanup
- Monthly: remote merged cleanup with approval
