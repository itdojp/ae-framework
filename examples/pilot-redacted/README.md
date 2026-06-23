# Redacted External Pilot Placeholder Example

This directory contains a synthetic, redacted placeholder for the first
report-only external pilot. It is not evidence from a live external repository.
Use it only to exercise the pilot runbook and evidence template before a
maintainer-approved pilot is available.

Related docs:

- `docs/product/PILOT-RUNBOOK-2026Q3.md`
- `docs/product/PILOT-EVIDENCE-TEMPLATE.md`
- `docs/guides/external-pilot-onboarding.md`

## Files

| File | Purpose |
| --- | --- |
| `pilot-evidence-log.example.csv` | Five placeholder PR rows with the required collection fields. |
| `pilot-pr-1.agent-pr-assurance-metrics.json` | Synthetic report-only metrics JSON for one redacted PR. |
| `pilot-pr-1.agent-pr-assurance-metrics.md` | Human-readable synthetic metrics surface. |
| `review-surface.example.md` | Minimal PR comment body that can be previewed with the posting helper. |

## Constraints

- Do not use this directory to claim that an external pilot has run.
- Do not replace `repo-redacted`, `pr-redacted`, or `reviewer-redacted` with live
  identifiers unless the pilot maintainer approves the publication boundary.
- Keep raw live pilot outputs outside public examples by default.
