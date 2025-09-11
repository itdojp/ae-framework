# CI Label Gating Policy

Purpose
- Enable gradual tightening of CI by toggling gates per PR using labels. Default remains non‑blocking to avoid disruption.

Labels
- `enforce-artifacts`: make artifacts validation (ajv) blocking
- `enforce-testing`: make testing scripts (property/replay/BDD lint) blocking
- `trace:<id>`: set TRACE_ID for focused runs in property/replay scripts
- `pr-summary:detailed`: render a more detailed PR summary (vs. digest)

Workflows
- validate-artifacts-ajv.yml: reads `enforce-artifacts` and toggles `continue-on-error`
- testing-ddd-scripts.yml: reads `enforce-testing` and toggles `continue-on-error`; reads `trace:<id>` to focus runs
- pr-summary-comment.yml: reads `pr-summary:detailed` to switch summary mode

Notes
- These controls are per‑PR. Organization/branch‑wide enforcement can be added later (e.g., always blocking on main) once agreed.
