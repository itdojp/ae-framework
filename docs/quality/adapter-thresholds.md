# Adapter Thresholds — Lighthouse/Perf/A11y (Label-Gated)

Purpose
- Define adapter thresholds and label-gated enforcement without slowing down PRs by default.

Proposal
- Keep adapter checks non-blocking on PRs; use labels to opt-in enforcement and/or stricter thresholds.
- Example labels (to be wired incrementally):
  - `enforce-a11y`, `enforce-perf`, `enforce-lh` — turn results into gates
  - `a11y:<score>`, `perf:<score>` — override thresholds ad hoc

Current wiring (a11y minimal)
- `run-adapters`: runs adapter-thresholds.yml to summarize `reports/a11y-results.json` on PR (non-blocking)
- `enforce-a11y`: enforces minimal thresholds (critical=0, serious=0). Job fails if violated.

Perf (proposal → minimal wiring)
- `reports/perf-results.json` が存在する場合にスコアを要約（非ブロッキング）
- `enforce-perf` ラベルでしきい値を強制（`perf:<score>` ラベルで上書き。既定は `vars.PERF_DEFAULT_THRESHOLD` または 75）
- Slash Commands: `/enforce-perf`, `/perf <pct|clear>`

Lighthouse (proposal → minimal wiring)
- `reports/lighthouse-results.json`（または `reports/lh-results.json`）から performance スコアを要約（非ブロッキング）
- `enforce-lh` ラベルでしきい値を強制（`lh:<score>` ラベルで上書き。既定は `vars.LH_DEFAULT_THRESHOLD` または 80）
- Slash Commands: `/enforce-lh`, `/lh <pct|clear>`

Phasing
- Phase 1: Reporting only (post PR comments/artifacts)
- Phase 2: Label-gated enforcement
- Phase 3: Consider main defaults after observation

Notes
- See `quality-gates-centralized.yml` for central jobs and consider adding thresholds as follow-up.
 - File: `.github/workflows/adapter-thresholds.yml`
