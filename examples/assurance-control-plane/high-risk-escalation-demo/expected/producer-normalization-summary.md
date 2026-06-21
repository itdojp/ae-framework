# Producer Normalization Summary

> Report-only: this summary does not approve, prove, or pass the producer output.

- Schema: `producer-normalization-summary/v1`
- Generated at: `2026-06-21T00:00:00.000Z`
- Input: `examples/assurance-control-plane/high-risk-escalation-demo/producer-output/codex-cli-high-risk-escalation-output.json`
- Producer: `codex-cli-high-risk-escalation` (Codex CLI local task with tenant-isolation claim gaps)
- Mode: `report-only`
- Control-plane decision emitted: `false`

## Expected artifact routing

- `producer-normalization-summary/v1` — Normalize raw Codex CLI high-risk claim output into report-only routing context.
- `claim-evidence-manifest/v1` — Show selected critical claims, missing evidence, unresolved status, and waiver metadata gaps.
- `assurance-summary/v1` — Render selected high-risk claim gaps as reviewer-facing assurance evidence without calling focused tests proof.
- `policy-gate-summary/v1` — Show fast-lane report-only behavior and strict high-risk blocking behavior for the same claim gaps.

## Missing evidence

- **command**: Command evidence is not complete: pnpm -s exec vitest run tests/property/auth/tenant-isolation-cross-tenant.test.ts --reporter dot (not-run-in-producer-output)
- **command**: Command evidence is not complete: node scripts/runtime/validate-tenant-isolation-control.mjs (not-run-in-producer-output)
- **claim-evidence**: Claim has no supporting evidence list: tenant-isolation-waiver-has-reviewable-metadata
- **waiver-metadata**: Waiver metadata is incomplete for claim tenant-isolation-waiver-has-reviewable-metadata: waiver.owner, waiver.reason, waiver.expiresAt

## Report-only findings

- `known-gap:ACP-HR-ESC-001` (known-gap): ACP-HR-ESC-001: Focused unit evidence does not satisfy adversarial/property and runtime-control requirements for a selected tenant-isolation claim.
- `known-gap:ACP-HR-ESC-002` (known-gap): ACP-HR-ESC-002: Waiver metadata gaps stay visible as reviewer actions and are blocking when strict assurance is selected.
- `missing-command:3` (missing-evidence): Command evidence is not complete: pnpm -s exec vitest run tests/property/auth/tenant-isolation-cross-tenant.test.ts --reporter dot (not-run-in-producer-output)
- `missing-command:4` (missing-evidence): Command evidence is not complete: node scripts/runtime/validate-tenant-isolation-control.mjs (not-run-in-producer-output)
- `missing-claim-evidence:2` (missing-evidence): Claim has no supporting evidence list: tenant-isolation-waiver-has-reviewable-metadata
- `missing-waiver-metadata:2` (waiver-metadata): Waiver metadata is incomplete for claim tenant-isolation-waiver-has-reviewable-metadata: waiver.owner, waiver.reason, waiver.expiresAt

## Claims mentioned by producer

- `tenant-isolation-enforced-before-account-read` → `claim-evidence-manifest/v1`
- `tenant-isolation-waiver-has-reviewable-metadata` → `claim-evidence-manifest/v1`
- `producer-summary-is-not-approval` → `policy-decision/v1`

## Unresolved notes

- ACP-HR-ESC-001: Focused unit evidence does not satisfy adversarial/property and runtime-control requirements for a selected tenant-isolation claim.
- ACP-HR-ESC-002: Waiver metadata gaps stay visible as reviewer actions and are blocking when strict assurance is selected.
- Tenant isolation is selected as a high-risk claim; missing adversarial and runtime-control evidence must remain visible when strict assurance is selected.
- The producer did not provide property/adversarial evidence for cross-tenant negative cases.
- The waiver record mentions an emergency exception but omits owner, reason, and expiry.
