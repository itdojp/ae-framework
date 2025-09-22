# Formal Aggregate PR Comment — Spec and Upsert Guide (Issue #961)

Status: Draft (docs-only)
Scope: Define a consistent, upserted PR comment for formal aggregate results.

Header and Upsert
- Fixed header: `<!-- AE-FORMAL-AGGREGATE -->`
- Upsert: find existing comment starting with the header; update if present, otherwise create.
- One comment per PR; re-runs overwrite content under the same header to avoid noise.

Sources and Minimal JSON
- Primary source: `artifacts/formal/formal-aggregate.json`
  - Minimal shape (example):
  ```json
  {
    "info": {
      "present": { "conformance": true, "smt": true, "alloy": false, "tla": true, "apalache": false },
      "presentCount": 3,
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

