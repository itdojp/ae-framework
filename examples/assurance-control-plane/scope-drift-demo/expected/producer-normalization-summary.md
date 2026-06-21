# Producer Normalization Summary

> Report-only: this summary does not approve, prove, or pass the producer output.

- Schema: `producer-normalization-summary/v1`
- Generated at: `2026-06-21T00:00:00.000Z`
- Input: `examples/assurance-control-plane/scope-drift-demo/producer-output/codex-cli-scope-drift-output.json`
- Producer: `codex-cli-scope-drift` (Codex CLI local task with scope drift)
- Mode: `report-only`
- Control-plane decision emitted: `false`

## Expected artifact routing

- `producer-normalization-summary/v1` — Normalize raw Codex CLI scope-drift output into report-only routing context.
- `context-pack-boundary-map-summary/v1` — Show changed-file and boundary drift as design-boundary evidence, not proof failure.
- `assurance-summary/v1` — Surface scope drift as reviewer action and residual risk in the review surface.
- `policy-gate-summary/v1` — Show normal-lane report-only behavior and strict high-risk blocking behavior without trusting producer text as approval.

## Missing evidence

- **command**: Command evidence is not complete: pnpm -s run context-pack:verify-boundary-map (not-run-in-producer-output)
- **claim-evidence**: Claim has no supporting evidence list: scope-drift-within-declared-boundary

## Report-only findings

- `known-gap:ACP-SCOPE-DRIFT-001` (known-gap): ACP-SCOPE-DRIFT-001: Out-of-scope changed files are reviewer evidence; they are not automatically proof failures or automatic blocks.
- `known-gap:ACP-SCOPE-DRIFT-002` (known-gap): ACP-SCOPE-DRIFT-002: Boundary Map drift is report-only by default and escalates only when risk/high-assurance policy selects enforcement.
- `missing-command:3` (missing-evidence): Command evidence is not complete: pnpm -s run context-pack:verify-boundary-map (not-run-in-producer-output)
- `missing-claim-evidence:1` (missing-evidence): Claim has no supporting evidence list: scope-drift-within-declared-boundary

## Claims mentioned by producer

- `scope-drift-within-declared-boundary` → `claim-evidence-manifest/v1`
- `producer-summary-is-not-approval` → `policy-decision/v1`

## Unresolved notes

- ACP-SCOPE-DRIFT-001: Out-of-scope changed files are reviewer evidence; they are not automatically proof failures or automatic blocks.
- ACP-SCOPE-DRIFT-002: Boundary Map drift is report-only by default and escalates only when risk/high-assurance policy selects enforcement.
- The producer did not explain why the payment settlement helper changed or provide evidence for that out-of-scope file.
- If the out-of-scope file were accepted as a payment or settlement change, reviewers would consider risk:high / enforce-assurance escalation.
