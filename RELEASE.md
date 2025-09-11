# Release Guide (Quality Artifacts)

When publishing a release, the workflow `release-quality-artifacts` bundles quality evidence:
- `artifacts/` (normalized adapter summaries, domain events, etc.)
- `formal/summary.json` (if present)
- `coverage/coverage-summary.json` (if present)
- `artifacts/summary/PR_SUMMARY.md`
- `artifacts/summary/combined.json` (if present)

Tips
- Ensure CI ran `testing-ddd-scripts` and `coverage-check` before tagging.
- Use labels to temporarily enforce gates on PRs: see `docs/ci/label-gating.md`.
