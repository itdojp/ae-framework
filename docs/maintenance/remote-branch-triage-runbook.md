# Remote Branch Triage Runbook

This runbook defines how to review and execute remote branch cleanup with operator approval.

Related:

- Branch cleanup: `docs/maintenance/branch-cleanup-runbook.md`
- Worktree cleanup: `docs/maintenance/worktree-cleanup-runbook.md`

## Scope

- Target repository: `ae-framework`
- Goal: separate remote merged safe-delete candidates from remote stale manual-triage candidates
- Safe default: **remote deletion is never automatic**

## Inputs and outputs

Source inventory:

- `tmp/maintenance/branch-inventory.json`
- `tmp/maintenance/branch-inventory.md`

Generated triage worksheet:

- `tmp/maintenance/remote-branch-triage.json`
- `tmp/maintenance/remote-branch-triage.md`

Key worksheet fields:

- `githubPullRequests`: lookup availability, requested limit/base, matched PR count
- GitHub PR lookup defaults to the inventory-derived base branch and ignores cross-repository PRs from forks
- `remoteMerged[*].latestPr`: latest linked PR summary for each merged remote branch
- `remoteMerged[*].deleteCommand`: operator-ready delete command
- `remoteStale[*].riskBand`: low / standard / high risk bucket
- `remoteStale[*].prState`: `open`, `closed`, `merged`, `none`, `ambiguous`, or `unavailable`
- `templates.issueComment`: reusable issue/PR comment template

## Commands

### 1) Refresh inventory

```bash
pnpm run maintenance:branch:inventory
```

### 2) Render triage worksheet

```bash
pnpm run maintenance:branch:triage:render

# Optional: disable GitHub PR lookup in offline/debug runs
node scripts/maintenance/remote-branch-triage.mjs --gh-pr-limit 0

# Optional: override auto-derived base branch filter
node scripts/maintenance/remote-branch-triage.mjs --gh-pr-base release/2026-03
```

### 3) Review decisions

- `remoteMerged`:
  - default proposal: `delete`
  - requires operator approval before execution
  - verify `latestPr`, `baseBranches`, and `deleteCommand` before apply
- `remoteStale`:
  - review `riskBand`, `prState`, and `proposedAction`
  - fill `decision` with one of `keep`, `archive`, `delete`
  - add `notes` explaining why the branch is retained or removed

### 4) Execute approved delete batch

```bash
# Reviewed merged rows
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-manifest-json tmp/maintenance/remote-branch-triage.json \
  --remote-manifest-mode merged \
  --max 100 \
  --apply

# Reviewed stale rows with decision=delete
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-manifest-json tmp/maintenance/remote-branch-triage.json \
  --remote-manifest-mode stale-delete \
  --max 100 \
  --apply
```

If only a subset of rows is approved, materialize that subset into a branch list and run:

```bash
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-branches-file tmp/maintenance/approved-remote-branches.txt \
  --max 100 \
  --apply
```

### 5) Re-run inventory after delete

```bash
pnpm run maintenance:branch:inventory
pnpm run maintenance:branch:triage:render
```

## Triage policy

### Remote merged candidates

- Delete when:
  - inventory still reports the branch as merged to `base`
  - no active release/hotfix workflow depends on the branch
  - operator approval is recorded

### Remote stale candidates

- `keep`:
  - linked PR is still `open`
  - still referenced by an active issue, plan, or long-running experiment
- `archive`:
  - high-risk prefix (`feat/*`, `feature/*`, `fix/*`, `ops/*`, `policy/*`) or non-trivial history remains
  - keep for historical comparison, but do not use for active development
- `delete`:
  - low-risk prefix (`docs/*`, `chore/*`, `test/*`, `ci/*`, `types/*`)
  - no active owner, no active issue, and no operational dependency remains

If `prState=ambiguous`, treat the worksheet row as branch-name reuse risk and keep manual review mandatory.

If `githubPullRequests.available=false`, treat `proposedAction` as advisory only and keep manual review strict.

## Approval checklist

- [ ] latest inventory reviewed
- [ ] triage worksheet rendered and archived
- [ ] remote merged candidates confirmed
- [ ] remote stale candidates classified with rationale
- [ ] operator approval recorded before `--scope remote --apply`
- [ ] post-delete inventory re-run completed
