# Remote Branch Triage Runbook

This runbook defines how to review and execute remote branch cleanup with operator approval.

Related:

- Branch inventory: `docs/maintenance/branch-cleanup-runbook.md`
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

## Commands

### 1) Refresh inventory

```bash
pnpm run maintenance:branch:inventory
```

### 2) Render triage worksheet

```bash
pnpm run maintenance:branch:triage:render
```

### 3) Review decisions

- `remoteMerged`:
  - default proposal: `delete`
  - requires operator approval before execution
- `remoteStale`:
  - fill `decision` with one of `keep`, `archive`, `delete`
  - add `notes` explaining why the branch is retained or removed

### 4) Execute approved delete batch

```bash
node scripts/maintenance/branch-cleanup.mjs --scope remote --max 100 --apply
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
  - still referenced by an active issue, plan, or long-running experiment
- `archive`:
  - keep for historical comparison, but do not use for active development
- `delete`:
  - no active owner, no active issue, and no operational dependency remains

## Approval checklist

- [ ] latest inventory reviewed
- [ ] triage worksheet rendered and archived
- [ ] remote merged candidates confirmed
- [ ] remote stale candidates classified with rationale
- [ ] operator approval recorded before `--scope remote --apply`
- [ ] post-delete inventory re-run completed
