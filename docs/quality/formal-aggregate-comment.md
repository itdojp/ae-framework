# Formal Aggregate PR Comment — Spec and Upsert Guide (Issue #961)

Status: Draft (docs-only)
Scope: Define a consistent, upserted PR comment for formal aggregate results.

Header and Upsert
- Fixed header: `<!-- AE-FORMAL-AGGREGATE -->`
- Upsert: find existing comment starting with the header; update if present, otherwise create.
- One comment per PR; re-runs overwrite content under the same header to avoid noise.

Permissions (workflow)
- To post/update the PR comment from a workflow, ensure permissions include:
  - `contents: read`
  - `issues: write`
  - `pull-requests: write`
  - Example (see `.github/workflows/formal-aggregate.yml`).
 - Recommended: set job-level `concurrency` (e.g., `formal-aggregate-${{ github.ref }}` with `cancel-in-progress: true`) to avoid racing duplicate runs; upsert remains idempotent.

Sources and Minimal JSON
- Primary source: `artifacts/formal/formal-aggregate.json`
  - Minimal shape (example):
  ```json
  {
    "info": {
      "present": { "conformance": true, "smt": true, "alloy": false, "tla": true, "apalache": false },
      "presentCount": 3,
      "presentKeys": ["conformance", "smt", "tla"],
      "ranOk": { "apalache": false },
      "errors": [
        { "tool": "apalache", "kind": "parse", "message": "...", "snippet": "..." }
      ]
    },
    "byType": { "conformance": { "schemaErrors": 0, "invariantViolations": 3, "violationRate": 0.30 } }
  }
  ```
- Secondary data (optional): `hermetic-reports/formal/summary.json` for concise one-line console summary.

Clamp and Limits (env)
- `FORMAL_AGG_LINE_CLAMP` (default 200): line clamp for long lines in comment body.
- `FORMAL_AGG_ERRORS_LIMIT` (default 5): max number of error fragments to include.
- `FORMAL_AGG_SNIPPET_MAX_LINES` (default 20): clamp for multi-line error snippets.
- `FORMAL_AGG_WRAP_WIDTH` (default 0 = disabled): soft-wrap width for long lines outside code fences (recommended 80–100 for readability).

Comment Structure (recommended)
1) Present — a compact presence tally and list
   - Format: `Present: <count>/5 (conformance, smt, alloy, tla, apalache)`
2) Summary — key numbers from `byType` when available
   - Example: `Conformance: schemaErrors=0, invariantViolations=3, rate=0.300`
3) By-type present — list tools present (same order), with quick statuses
   - Example: `By-type present: conformance, smt, tla`
4) Apalache ran/ok — single-line status if available
   - Example: `Apalache: ran=false, ok=false` (when present)
5) Meta — Tools/Reproduce/Policy/Clamp/Generated
   - Tools: present flags; Reproduce: short CLI (verify:tla/smt/alloy); Policy: label-gated, non-blocking; Clamp: env values; Generated: timestamp

One-line Summary (top)
- Optional first line: `Formal aggregate: Present 3/5 | Conformance iv=3 (rate=0.300) | Apalache ran=false`
- Keep within clamp; reduce detail if exceeded.

Sample Body
```
<!-- AE-FORMAL-AGGREGATE -->
Formal aggregate: Present 3/5 | Conformance iv=3 (rate=0.300) | Apalache ran=false

Present
- conformance, smt, tla (3/5)

Summary
- Conformance: schemaErrors=0, invariantViolations=3, rate=0.300, first=allocated_le_onhand@2, byType(onhand_min=1, allocated_le_onhand=2)

Apalache
- ran=false, ok=false

Meta
- Tools: present={conformance,smt,tla}, alloy/apalache absent
- Reproduce: `pnpm run verify:tla -- --engine=tlc` | `pnpm run verify:smt -- --solver=z3` | `pnpm run verify:alloy`
- Policy: non-blocking (label-gated: run-formal; enforce: enforce-formal)
- Clamp: FORMAL_AGG_LINE_CLAMP=200, FORMAL_AGG_ERRORS_LIMIT=5, FORMAL_AGG_SNIPPET_MAX_LINES=20
- Generated: 2025-09-20T12:34:56Z
```

Upsert Snippet (GitHub Script)
```js
const header = '<!-- AE-FORMAL-AGGREGATE -->';
const { owner, repo } = context.repo;
const issue_number = context.issue.number;
const comments = await github.rest.issues.listComments({ owner, repo, issue_number, per_page: 100 });
const existing = comments.data.find(c => typeof c.body === 'string' && c.body.startsWith(header));
const body = header + '\n' + renderAggregateBody();
if (existing) {
  await github.rest.issues.updateComment({ owner, repo, comment_id: existing.id, body });
} else {
  await github.rest.issues.createComment({ owner, repo, issue_number, body });
}
```

Consistency
- Aligns with: `docs/quality/formal-runbook.md` guidance and `AGENTS.md` comment header policy。
- Non-blocking by default; labels: `run-formal` (run), `enforce-formal` (optional enforcement).

## Validation (PR Walkthrough)

1) Label-gated run (report-only)
- On a draft PR, comment `/run-formal` (adds label `run-formal`).
- Expect: `formal-aggregate.yml` runs under `pull_request` and posts an upserted comment starting with `<!-- AE-FORMAL-AGGREGATE -->`.

2) Re-run (idempotent)
- Comment `/run-formal` again (no change in labels) or push a new commit (synchronize event).
- Expect: the same header comment is updated (not duplicated).

3) Manual dispatch (artifacts only)
- Comment `/formal-aggregate-dispatch` to trigger `workflow_dispatch` on PR head.
- Expect: artifacts `artifacts/formal/formal-aggregate.{md,json}` are generated. Comment posting occurs only on `pull_request` runs.

4) Env tuning (optional)
- Set clamp envs to adjust formatting: `FORMAL_AGG_LINE_CLAMP` (default 200), `FORMAL_AGG_ERRORS_LIMIT` (default 5), `FORMAL_AGG_SNIPPET_MAX_LINES` (default 20).

## Troubleshooting

- No aggregate found: ensure label `run-formal` is present and that the workflow ran under `pull_request` (not just dispatch).
- Validate JSON locally (non-blocking):
  - `node scripts/formal/validate-aggregate-json.mjs` (warns on missing/invalid `artifacts/formal/formal-aggregate.json`)
- Clamp looks too aggressive: raise `FORMAL_AGG_LINE_CLAMP` or `FORMAL_AGG_ERRORS_LIMIT` in the workflow env or rerun with overrides.

## Artifacts (expected)

- formal-reports-aggregate (artifact): `artifacts/formal/formal-aggregate.md`
- formal-reports-aggregate-json (artifact): `artifacts/formal/formal-aggregate.json`
- Tips: Download both artifacts from the Actions run to inspect the exact MD/JSON posted/derived.

## FAQ

- Q: DispatchしたのにPRコメントが出ないのはなぜ？
  - A: `workflow_dispatch` はArtifactsのみ生成します。PRコメントのアップサートは `pull_request` 実行かつ `run-formal` ラベル時に行われます。
- Q: 同じコメントが重複しませんか？
  - A: 固定ヘッダ `<!-- AE-FORMAL-AGGREGATE -->` に対してアップサート（上書き）します。本文が同一の場合は更新をスキップします。
- Q: 行が長くて読みにくい場合は？
  - A: `FORMAL_AGG_WRAP_WIDTH`（推奨 80–100）や `FORMAL_AGG_LINE_CLAMP` を調整してください。

## Quick triage (jq)

Extract present count and keys
```
jq -r '.info.presentCount' artifacts/formal/formal-aggregate.json
jq -r '(.info.presentKeys // (.info.present | to_entries | map(select(.value)) | map(.key))) | join(", ")' artifacts/formal/formal-aggregate.json
```

Apalache ran/ok (if present)
```
jq -r '.info.ranOk.apalache' artifacts/formal/formal-aggregate.json
```

Conformance summary (if present)
```
jq -r '.conformance | {schemaErrors, invariantViolations, violationRate}' artifacts/formal/formal-aggregate.json
```

## Verify PR comment via GitHub CLI

Check for the upserted comment (by fixed header):
```
gh pr view <pr-number> --json comments --jq '.comments[].body | select(startswith("<!-- AE-FORMAL-AGGREGATE -->"))'
```

Count matching comments (should be 0 or 1 due to upsert):
```
gh pr view <pr-number> --json comments --jq '.comments[].body | select(startswith("<!-- AE-FORMAL-AGGREGATE -->"))' | wc -l
```

## Workflow outputs (for reuse)

- The aggregate workflow exports selected fields for downstream jobs:
  - `present_count`: integer (0..5)
  - `present_keys`: CSV (ordered keys present)
  - `aggregate_json_present`: `true|false`
  - `comment_action`: `created|updated|skipped`
  - `comment_url`: URL of the PR comment (when created/updated)
  - `comment_reason`: reason when skipped (e.g., `no-md`, `no-json`, `unchanged`)
  - `comment_present`: `1|0` (whether the PR already has the aggregate comment after this run)
  - `has_run_formal`: `1|0` (whether the PR currently has `run-formal` label)

Downstream usage (example)
```yaml
jobs:
  aggregate:
    uses: ./.github/workflows/formal-aggregate.yml
  consume:
    needs: aggregate
    runs-on: ubuntu-latest
    steps:
      - run: |
          echo "present_count=${{ needs.aggregate.outputs.present_count }}"
          echo "present_keys=${{ needs.aggregate.outputs.present_keys }}"
          echo "comment_action=${{ needs.aggregate.outputs.comment_action }}"
          echo "comment_url=${{ needs.aggregate.outputs.comment_url }}"
```

## GitHub Step Summary (reviewer hints)

- The workflow appends a brief Step Summary to help reviewers verify runs without opening artifacts:
  - `Present: <count>/5`
  - `Keys: <comma-separated present keys>`
  - `Apalache: ran=yes|no ok=yes|no|n/a`
  - `Conformance: schemaErrors=X, invariantViolations=Y, rate=Z` (when present)
  - `Artifacts: artifacts/formal/formal-aggregate.{md,json}`
  - `Header: <!-- AE-FORMAL-AGGREGATE --> (upsert on pull_request with label run-formal)`
  - `Docs: docs/quality/formal-aggregate-comment.md`
  - `Runbook: docs/quality/formal-runbook.md`
  - `Run: <workflow run URL>`
  - `Clamp: line=…, errors=…, snippet=…, wrap=…`
  - `Comment: created|updated|skipped` (+ URL/reason when available)

### Comment skip reasons (reference)

- `unchanged`: existing PR comment body is identical to the newly generated content (idempotent upsert skips update)
- `no-md`: aggregate markdown (`artifacts/formal/formal-aggregate.md`) was not found in this run context
- `no-json`: aggregate JSON (`artifacts/formal/formal-aggregate.json`) was not found in this run context
- `api-error`: GitHub API error occurred during comment create/update (see workflow logs for details)

## Dispatch via GitHub CLI (artifacts only)

Run the aggregate workflow on a PR head branch (does not post the PR comment):
```
gh workflow run formal-aggregate.yml --ref <head-branch>
```

Monitor the run:
```
gh run list --workflow "Formal Reports Aggregate" --limit 1
gh run watch <run-id>
```
