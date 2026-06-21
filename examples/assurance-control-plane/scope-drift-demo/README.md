# Scope Drift Assurance Demo

This example is the fixture-backed scenario pack for Issue #3511 / ACP-084. It
shows how ae-framework surfaces agent-generated scope drift as reviewer evidence
without treating producer text as approval or automatic failure.

The scenario is offline. It does not call an external LLM API, hosted agent
service, GitHub API, or GitHub Actions.

## Scenario

A sample Issue asks the producer to update reservation-audit reviewer guidance
and one focused test. The intended scope is:

- `docs/inventory/reservation-audit.md`
- `tests/unit/inventory/reservation-audit.test.ts`
- `examples/assurance-control-plane/scope-drift-demo/**`

The raw producer output also reports this out-of-scope file:

- `src/payments/settlement-retry.ts`

The demo treats that file as **scope drift evidence**. It does not call the agent
malicious and it does not infer proof failure. Reviewers decide whether to reject
the drift, request changes, or intentionally escalate the changed scope.

## Flow

```text
sample Issue / task description
  -> Codex CLI raw producer output fixture with an out-of-scope changed file
  -> producer-normalization-summary/v1
  -> context-pack-boundary-map-summary/v1 with drift findings
  -> assurance-summary/v1 reviewer surface
  -> policy-gate-summary/v1 normal and high-risk interpretations
  -> artifacts/review/scope-drift-demo/assurance-review.md
```

## Run

From the repository root:

```bash
node scripts/demo/run-scope-drift-demo.mjs
```

Use `--output-root <path>` for isolated output under the repository root:

```bash
node scripts/demo/run-scope-drift-demo.mjs \
  --output-root artifacts/my-scope-drift-demo \
  --generated-at 2026-06-21T00:00:00.000Z
```

Default outputs:

| Artifact | Path |
| --- | --- |
| Producer normalization summary | `artifacts/agents/scope-drift-demo/producer-normalization-summary.json` |
| Boundary Map report | `artifacts/context-pack/scope-drift-demo/context-pack-boundary-map-report.json` |
| Boundary Map summary | `artifacts/context-pack/scope-drift-demo/boundary-map-summary.json` |
| Assurance summary | `artifacts/assurance/scope-drift-demo/assurance-summary.json` |
| High-risk plan artifact | `artifacts/plan/scope-drift-demo/high-risk-plan-artifact.json` |
| Plan artifact validation | `artifacts/plan/scope-drift-demo/plan-artifact-validation.json` |
| Normal policy summary | `artifacts/policy/scope-drift-demo/policy-gate-summary.normal.json` |
| High-risk policy summary | `artifacts/policy/scope-drift-demo/policy-gate-summary.high-risk.json` |
| Normal reviewer surface | `artifacts/review/scope-drift-demo/assurance-review.md` |
| High-risk reviewer surface | `artifacts/review/scope-drift-demo/assurance-review.high-risk.md` |

Expected golden fixtures live in `expected/`.

## What reviewers should inspect

1. **Producer / task scope** — the changed-file table shows both intended files
   and the out-of-scope payment file.
2. **Boundary / scope status** — `boundary_map_status=drift` and
   `scope_drift_finding_count=2` are visible before raw logs.
3. **Missing evidence / unresolved claims** — the producer did not provide a
   Boundary Map verification command or supporting evidence for accepting the
   out-of-scope payment file.
4. **Policy decision** — normal lane remains report-only; high-risk strict lane
   blocks because `boundary-map-drift` is unresolved.

## Policy behavior

| Lane | Expected policy output | Meaning |
| --- | --- | --- |
| Normal PR / `risk:low` | `policy-gate-summary.normal.json` has `evaluation.ok=true` and `assurance.result=report-only`. | Scope drift is reviewer context. It should be fixed or explicitly accepted, but the fixture does not create an automatic block. |
| High-risk strict / `risk:high` + `enforce-assurance` | `policy-gate-summary.high-risk.json` has `evaluation.ok=false` and `assurance.result=block`. | When strict assurance is selected, unresolved `boundary-map-drift` becomes a blocking reviewer action until evidence or waiver is supplied. |

This distinction is the point of the scenario: ae-framework keeps ordinary PRs on
the fast lane while preserving enough evidence for selected high-risk escalation.

## False-positive and boundary limits

Boundary Map evidence is a review aid, not a semantic diff engine. A drift row can
be a false positive if the Issue scope was incomplete or the Boundary Map did not
model a legitimate dependency. In that case, reviewers should update the Issue,
Context Pack, Boundary Map, or waiver rationale rather than silently ignoring the
finding.

Out-of-scope changes are not automatically agent failures. They are evidence that
reviewers need a disposition: reject, split into a separate Issue, accept with
rationale, or escalate.
