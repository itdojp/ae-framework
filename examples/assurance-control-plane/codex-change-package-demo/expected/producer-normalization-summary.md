# Producer Normalization Summary

> Report-only: this summary does not approve, prove, or pass the producer output.

- Schema: `producer-normalization-summary/v1`
- Generated at: `2026-06-20T00:00:00.000Z`
- Input: `examples/assurance-control-plane/codex-change-package-demo/producer-output/codex-cli-task-output.json`
- Producer: `codex-cli` (Codex CLI local task)
- Mode: `report-only`
- Control-plane decision emitted: `false`

## Expected artifact routing

- `producer-normalization-summary/v1` — Normalize raw Codex CLI output into report-only routing context.
- `change-package/v2` — Summarize changed files, commands, requirement/claim scope, and reviewer evidence.
- `assurance-summary/v1` — Surface producer report-only findings and residual risks in the reviewer decision surface.
- `policy-gate-summary/v1` — Show policy-gate report-only findings without treating producer output as a blocking decision for the fast lane.

## Missing evidence

- **command**: Command evidence is not complete: pnpm -s run check:schemas (not-run-in-producer-output)
- **claim-evidence**: Claim has no supporting evidence list: schema-validation-evidence-present

## Report-only findings

- `known-gap:ACP-GAP-002` (known-gap): ACP-GAP-002: Raw producer output is routed by a report-only normalizer; it does not become a new guarantee vocabulary.
- `known-gap:ACP-GAP-003` (known-gap): ACP-GAP-003: Reviewer surfaces should expose missing evidence and gap IDs without requiring heavy lanes for ordinary fast-lane changes.
- `known-gap:ACP-GAP-004` (known-gap): ACP-GAP-004: Policy Gate may consume normalized findings as report-only context before enforcement escalation is selected.
- `missing-command:3` (missing-evidence): Command evidence is not complete: pnpm -s run check:schemas (not-run-in-producer-output)
- `missing-claim-evidence:2` (missing-evidence): Claim has no supporting evidence list: schema-validation-evidence-present

## Claims mentioned by producer

- `reservation-audit-trace-recorded` → `claim-evidence-manifest/v1`
- `schema-validation-evidence-present` → `claim-evidence-manifest/v1`
- `producer-summary-is-not-approval` → `policy-decision/v1`

## Unresolved notes

- ACP-GAP-002: Raw producer output is routed by a report-only normalizer; it does not become a new guarantee vocabulary.
- ACP-GAP-003: Reviewer surfaces should expose missing evidence and gap IDs without requiring heavy lanes for ordinary fast-lane changes.
- ACP-GAP-004: Policy Gate may consume normalized findings as report-only context before enforcement escalation is selected.
- The producer did not run schema validation; downstream control-plane artifacts must keep this as missing evidence.
- The sample is a fast-lane docs/tests demo; payment settlement, authz, or critical-core data migration changes would require risk:high / enforce-assurance escalation.
