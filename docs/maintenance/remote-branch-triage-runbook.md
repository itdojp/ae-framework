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
- `githubPullRequests.lookupCoverage` / `githubPullRequests.partialResults`: whether the GH lookup window was complete or truncated
- GitHub PR lookup defaults to the inventory-derived base branch and ignores cross-repository PRs from forks
- `remoteMerged[*].branchOid` / `remoteStale[*].branchOid`: inventory-captured remote tip SHA used as linkage evidence
- `remoteMerged[*].latestPr`: latest linked PR summary for each merged remote branch
- `remoteMerged[*].prMatchMode` / `remoteStale[*].prMatchMode`: `head-oid`, `branch-name-only`, or `none`
- `summary.staleByMatchMode`: stale branch counts grouped by linkage evidence quality
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

# Optional: widen the GH lookup window when coverage is reported as truncated
node scripts/maintenance/remote-branch-triage.mjs --gh-pr-limit 2000

# Optional: override auto-derived base branch filter
node scripts/maintenance/remote-branch-triage.mjs --gh-pr-base release/2026-03
```

### 3) Review decisions

- `remoteMerged`:
  - default proposal: `delete`
  - requires operator approval before execution
  - verify `branchOid`, `prMatchMode`, `latestPr`, `baseBranches`, and `deleteCommand` before apply
- `remoteStale`:
  - review `branchOid`, `riskBand`, `prState`, `prMatchMode`, and `proposedAction`
  - fill `decision` with one of `keep`, `archive`, `delete`
  - add `notes` explaining why the branch is retained or removed

### 3.5) Render batch review packs

```bash
pnpm run maintenance:branch:triage:batches

# Optional: render from an alternate worksheet or output directory
node scripts/maintenance/remote-cleanup-batches.mjs \
  --input-json tmp/maintenance/remote-branch-triage.json \
  --output-dir tmp/maintenance/remote-cleanup-batches
```

Generated review packs:

- `tmp/maintenance/remote-cleanup-batches/summary.json`
- `tmp/maintenance/remote-cleanup-batches/summary.md`
- `tmp/maintenance/remote-cleanup-batches/issue-comment.md`
- `tmp/maintenance/remote-cleanup-batches/batch-a-merged.*`
- `tmp/maintenance/remote-cleanup-batches/batch-b-low-risk-stale.*`
- `tmp/maintenance/remote-cleanup-batches/batch-c-ambiguous-stale.*`
- For Batch B and C, `*.csv` files are also generated; the operator should edit the `decision` and `notes` fields in the CSV rather than in the JSON.

Batch semantics:

- Batch A: current `remoteMerged[*]` rows. Use the generated `*.commands.sh` only after operator approval.
- Batch B: low-risk prefixes (`docs/`, `chore/`, `test/`, `ci/`, `types/`) excluding `prState=ambiguous`.
- Batch C: `prState=ambiguous` rows isolated for manual inspection.

### 3.6) Audit active issue / automation references

```bash
pnpm run maintenance:branch:triage:reference-audit

# Optional: audit an alternate batch directory or run offline with a fixture
node scripts/maintenance/remote-cleanup-reference-audit.mjs \
  --batch-dir tmp/maintenance/remote-cleanup-batches \
  --output-dir tmp/maintenance/remote-cleanup-reference-audit

# Optional: ignore the tracking issue itself when its body/comment lists example branches
node scripts/maintenance/remote-cleanup-reference-audit.mjs \
  --batch-dir tmp/maintenance/remote-cleanup-batches \
  --output-dir tmp/maintenance/remote-cleanup-reference-audit \
  --ignore-issue-number 2469
```

Generated audit outputs:

- `tmp/maintenance/remote-cleanup-reference-audit/summary.json`
- `tmp/maintenance/remote-cleanup-reference-audit/summary.md`
- `tmp/maintenance/remote-cleanup-reference-audit/issue-comment.md`
- `tmp/maintenance/remote-cleanup-reference-audit/*.audit.json`
- `tmp/maintenance/remote-cleanup-reference-audit/*.audit.md`

Live issue lookup paginates open issues and per-issue comments before matching branch names.
Use `--open-issues-json` when a fixed offline fixture is preferable for review or regression.

Audit semantics:

- `openIssueRefs`: current open issue / PR title, body, comment matches
- `repoRefs`: tracked repository references grouped as `automation`, `plan`, `code`, `history`
- `reviewHint`:
  - `keep-review` when open issue refs or automation refs exist, including ambiguous rows
  - `manual-review` when no open issue/automation refs remain and plan/code refs still exist, or the row is ambiguous
  - `delete-candidate` / `archive-candidate` only when no active refs were found in the current audit scope

### 3.7) Render a consolidated Batch C evidence bundle

```bash
pnpm run maintenance:branch:triage:ambiguous-evidence

# Optional: use alternate batch / audit / output paths
node scripts/maintenance/remote-cleanup-ambiguous-evidence.mjs \
  --batch-json tmp/maintenance/remote-cleanup-batches/batch-c-ambiguous-stale.json \
  --audit-json tmp/maintenance/remote-cleanup-reference-audit/batch-c-ambiguous-stale.audit.json \
  --output-dir tmp/maintenance/remote-cleanup-ambiguous-evidence
```

Generated outputs:

- `tmp/maintenance/remote-cleanup-ambiguous-evidence/summary.json`
- `tmp/maintenance/remote-cleanup-ambiguous-evidence/summary.md`
- `tmp/maintenance/remote-cleanup-ambiguous-evidence/issue-comment.md`
- `tmp/maintenance/remote-cleanup-ambiguous-evidence/ambiguous-evidence.csv`

Bundle semantics:

- Validates that Batch C review pack provenance still matches the corresponding audit payload
- Consolidates `prMatchMode`, `latestPr`, `baseBranches`, and reference-audit counts into one operator-facing sheet
- Remains evidence-only; decisions stay in `batch-c-ambiguous-stale.csv`
- Reduces branch-name reuse ambiguity before manual `keep` / `archive` / `delete` entry

### 3.8) Sync reviewed batch decisions back into a derived manifest

```bash
pnpm run maintenance:branch:triage:decision-sync

# Optional: use alternate source / batch / output paths
node scripts/maintenance/remote-cleanup-decision-sync.mjs \
  --input-json tmp/maintenance/remote-branch-triage.json \
  --batch-dir tmp/maintenance/remote-cleanup-batches \
  --output-dir tmp/maintenance/remote-cleanup-reviewed
```

Generated outputs:

- `tmp/maintenance/remote-cleanup-reviewed/reviewed-triage.json`
- `tmp/maintenance/remote-cleanup-reviewed/summary.json`
- `tmp/maintenance/remote-cleanup-reviewed/summary.md`
- `tmp/maintenance/remote-cleanup-reviewed/issue-comment.md`

Sync semantics:

- Batch B / C `decision` and `notes` are copied back into `remoteStale[*]` by `branch`
- `branchOid` mismatch is treated as a hard error to avoid syncing stale review input into a moved branch
- If `batch-b-low-risk-stale.csv` / `batch-c-ambiguous-stale.csv` exist, prefer the CSV `decision` / `notes` values and reconcile them against the corresponding JSON provenance / row set
- `reviewed-triage.json` / `summary.json` retain `sourceBatches` and `reviewInputFormat`, allowing you to audit which review input was used for the sync
- this step records reviewed decisions only; it does not execute any delete command

### 3.9) Render delete readiness status from reviewed decisions + reference audit

```bash
pnpm run maintenance:branch:triage:review-status

# Optional: use alternate reviewed manifest / audit / output paths
node scripts/maintenance/remote-cleanup-review-status.mjs \
  --reviewed-manifest-json tmp/maintenance/remote-cleanup-reviewed/reviewed-triage.json \
  --reference-audit-dir tmp/maintenance/remote-cleanup-reference-audit \
  --output-dir tmp/maintenance/remote-cleanup-review-status
```

Generated outputs:

- `tmp/maintenance/remote-cleanup-review-status/summary.json`
- `tmp/maintenance/remote-cleanup-review-status/summary.md`
- `tmp/maintenance/remote-cleanup-review-status/issue-comment.md`
- `tmp/maintenance/remote-cleanup-review-status/delete-ready.json`
- `tmp/maintenance/remote-cleanup-review-status/delete-ready.md`
- `tmp/maintenance/remote-cleanup-review-status/delete-ready.branches.txt`
- `tmp/maintenance/remote-cleanup-review-status/delete-ready.branches.json`
- `tmp/maintenance/remote-cleanup-review-status/delete-blocked.json`
- `tmp/maintenance/remote-cleanup-review-status/pending-review.json`
- `tmp/maintenance/remote-cleanup-review-status/retained.json`
- `tmp/maintenance/remote-cleanup-review-status/missing-audit.json`

Status semantics:

- `delete-ready`: `decision=delete` and no open issue / automation / plan / code refs detected
- `delete-blocked`: `decision=delete` but active refs remain
- `retained`: `decision=keep|archive`
- `pending-review`: `decision` not set
- `missing-audit`: present in reviewed manifest but missing from reference audit

### 3.10) Render operator execution pack from delete-ready status

```bash
pnpm run maintenance:branch:triage:execution-pack

# Optional: use alternate review-status / output paths
node scripts/maintenance/remote-cleanup-execution-pack.mjs \
  --review-status-dir tmp/maintenance/remote-cleanup-review-status \
  --output-dir tmp/maintenance/remote-cleanup-execution-pack \
  --base origin/main \
  --remote origin \
  --max 100
```

Generated outputs:

- `tmp/maintenance/remote-cleanup-execution-pack/summary.json`
- `tmp/maintenance/remote-cleanup-execution-pack/summary.md`
- `tmp/maintenance/remote-cleanup-execution-pack/issue-comment.md`
- `tmp/maintenance/remote-cleanup-execution-pack/approved-remote-branches.json`
- `tmp/maintenance/remote-cleanup-execution-pack/branch-cleanup-dry-run-report.json`
- `tmp/maintenance/remote-cleanup-execution-pack/commands.sh`
- `tmp/maintenance/remote-cleanup-execution-pack/apply-command.txt`

Notes:

- this step does not execute remote delete
- `approved-remote-branches.json` is a self-contained copy of the reviewed delete-ready subset with provenance metadata
- `commands.sh` runs the exact dry-run command only
- `apply-command.txt` renders the exact apply command that stays scoped to the approved subset
- if `delete-ready` rows exceed `--max`, the script fails instead of generating a partial execution pack
- run the generated dry-run command and archive `branch-cleanup-dry-run-report.json` before operator-approved apply

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
  --remote-manifest-json tmp/maintenance/remote-cleanup-reviewed/reviewed-triage.json \
  --remote-manifest-mode stale-delete \
  --max 100 \
  --apply

# Narrow explicit subset rendered from delete-ready review status
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-branches-file tmp/maintenance/remote-cleanup-review-status/delete-ready.branches.json \
  --max 100 \
  --apply

# Preferred operator bundle rendered from the execution pack
bash tmp/maintenance/remote-cleanup-execution-pack/commands.sh

# After operator approval, run the exact apply command rendered in the pack
cat tmp/maintenance/remote-cleanup-execution-pack/apply-command.txt
```

If only a subset of rows is approved, materialize that subset into a branch list and run:

```bash
node scripts/maintenance/branch-cleanup.mjs \
  --scope remote \
  --remote-branches-file tmp/maintenance/approved-remote-branches.txt \
  --max 100 \
  --apply
```

The reviewed manifest path is accepted only when the triage JSON still records
`sourceInventory.remote` and `sourceInventory.base`, so the cleanup run stays
bound to the reviewed environment.

### 5) Verify the apply report against live remote refs

```bash
pnpm run maintenance:branch:cleanup:post-verify

# Optional: use an explicit branch-cleanup apply report path
node scripts/maintenance/remote-cleanup-post-apply-verify.mjs \
  --cleanup-report-json tmp/maintenance/branch-cleanup-report.json \
  --output-dir tmp/maintenance/remote-cleanup-post-apply-verify
```

Generated outputs:

- `tmp/maintenance/remote-cleanup-post-apply-verify/summary.json`
- `tmp/maintenance/remote-cleanup-post-apply-verify/summary.md`
- `tmp/maintenance/remote-cleanup-post-apply-verify/issue-comment.md`

Interpretation:

- `verified-absent`: branches reported as deleted and no longer present on the live remote
- `still-present`: branches reported as deleted but still present on the live remote; investigate before continuing
- `failed deletes`: branches already reported as failed by `branch-cleanup`
- `planned but not deleted`: reviewed branches that were planned but neither deleted nor failed in the apply report

### 6) Re-run inventory after delete

```bash
pnpm run maintenance:branch:inventory
pnpm run maintenance:branch:triage:render
```

### 7) Audit the refreshed triage for cleanup closure

```bash
pnpm run maintenance:branch:cleanup:refresh-audit

# Optional: use explicit post-verify / triage paths
node scripts/maintenance/remote-cleanup-refresh-audit.mjs \
  --post-verify-summary-json tmp/maintenance/remote-cleanup-post-apply-verify/summary.json \
  --refreshed-triage-json tmp/maintenance/remote-branch-triage.json \
  --output-dir tmp/maintenance/remote-cleanup-refresh-audit
```

Generated outputs:

- `tmp/maintenance/remote-cleanup-refresh-audit/summary.json`
- `tmp/maintenance/remote-cleanup-refresh-audit/summary.md`
- `tmp/maintenance/remote-cleanup-refresh-audit/issue-comment.md`

Interpretation:

- `confirmed-removed`: a previously `verified-absent` branch no longer appears in refreshed `remoteMerged` / `remoteStale`
- `reappeared-in-triage`: a previously `verified-absent` branch still appears in refreshed cleanup candidates and needs manual follow-up

This step is a closure audit only. It performs no deletion.

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

If `prMatchMode=branch-name-only`, do not treat `latestPr` as proven linkage; it is reference context only until OID evidence is confirmed.

If `githubPullRequests.lookupCoverage=truncated`, treat every `prState=none` row as incomplete evidence until the lookup window is widened and the worksheet is regenerated.

If `githubPullRequests.available=false`, treat `proposedAction` as advisory only and keep manual review strict.

## Approval checklist

- [ ] latest inventory reviewed
- [ ] triage worksheet rendered and archived
- [ ] remote merged candidates confirmed
- [ ] remote stale candidates classified with rationale
- [ ] execution pack dry-run archived
- [ ] operator approval recorded before `--scope remote --apply`
- [ ] post-apply verification archived
- [ ] post-delete inventory re-run completed
- [ ] refresh-audit bundle archived
