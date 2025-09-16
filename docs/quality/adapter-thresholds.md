# Adapter Thresholds — Lighthouse/Perf/A11y (Label-Gated)

Purpose
- Define adapter thresholds and label-gated enforcement without slowing down PRs by default.

Proposal
- Keep adapter checks non-blocking on PRs; use labels to opt-in enforcement and/or stricter thresholds.
- Example labels (to be wired incrementally):
  - `enforce-a11y`, `enforce-perf`, `enforce-lh` — turn results into gates
  - `a11y:<score>`, `perf:<score>` — override thresholds ad hoc

Phasing
- Phase 1: Reporting only (post PR comments/artifacts)
- Phase 2: Label-gated enforcement
- Phase 3: Consider main defaults after observation

Notes
- See `quality-gates-centralized.yml` for central jobs and consider adding thresholds as follow-up.

