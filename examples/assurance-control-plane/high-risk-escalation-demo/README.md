# High-risk escalation assurance demo

This fixture demonstrates ACP-085: selected critical claims can be escalated without forcing heavy verification on every PR.

## What the demo shows

- Domain: tenant isolation.
- Fast lane: missing adversarial/runtime evidence and waiver metadata gaps are rendered as report-only reviewer context.
- High-risk strict lane: the same selected tenant-isolation gaps become a blocking assurance result when `risk:high` and `enforce-assurance` select strict policy behavior.
- Producer output remains untrusted input. The review surface never treats a producer completion message, a focused unit test, or green baseline checks as proof.

## Run locally

```bash
node scripts/demo/run-high-risk-escalation-demo.mjs
```

The command writes fixture-backed artifacts under `artifacts/{agents,assurance,policy,review}/high-risk-escalation-demo` by default and does not require network access, a hosted LLM API, or a GitHub token.

## Reviewer path

1. Open `artifacts/review/high-risk-escalation-demo/assurance-review.md` for the normal fast lane.
2. Open `artifacts/review/high-risk-escalation-demo/assurance-review.high-risk.md` for the high-risk strict lane.
3. Inspect the selected critical claims section before raw logs.
4. Verify that required evidence kinds are distinct from claim status:
   - `unit`/focused behavior evidence is not `proof`.
   - `waived` is an exception state, not a satisfied claim.
   - Missing waiver owner, reason, and expiry remain reviewer actions.

## Policy interpretation

- `risk:low` / ordinary PR: report-only; no heavy lane is required by default.
- `risk:high`: human approval and a valid plan artifact are required.
- `enforce-assurance`: strict mode blocks missing required evidence, unresolved claims, failed evidence, and incomplete waiver metadata.

This demo is fixture-only. It does not implement a production authorization engine, new formal verifier, database migration, or production policy change.
