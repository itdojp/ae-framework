# Generated Tests & Features — Placement and Naming

Purpose
- Keep generated artifacts discoverable, diff-friendly, and easy to revert.

Guidelines
- Pathing
  - Tests: `tests/generated/**` (or `tests/<domain>/generated/**` when domain-specific)
  - Features: `features/generated/**` (if using BDD/feature files)
  - Artifacts: `artifacts/<domain>/**` (JSON/CSV summaries)
- Naming
  - Use stable IDs in filenames, e.g. `generated-<category>-<slug>.test.ts`
  - Include a short scenario slug; avoid timestamps in filenames (use inside file/JSON instead)
- Versioning
  - Include schema/version fields inside JSON artifacts
  - Prefer deterministic field order for snapshots
- CI
  - Generated files are not required for PRs; keep heavy generation opt-in via labels
  - Summaries funnel into `artifacts/summary/combined.json` when possible

Small PRs
- Add or replace generated test files in tiny batches
- Keep revertability: do not co-mingle generation with unrelated code changes
