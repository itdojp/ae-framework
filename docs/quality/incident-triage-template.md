# Incident Triage Template

Purpose: Provide a minimal, repeatable format for incident triage in AI-assisted development.

When to use:
- CI failures with unclear root cause
- Regression detected after merge
- Production or staging anomaly

## Triage summary (fill in)

- Incident ID / Link:
- Detected by (CI, monitoring, user report):
- First observed time (UTC):
- Affected area (module/service):
- Severity (low/medium/high/critical):
- Current status (open/mitigating/resolved):

## Evidence snapshot

- Failing checks / logs:
- Related PR(s) / commit(s):
- Reproduction steps:
- Artifacts (reports, traces, coverage, trends):

## Diagnosis

- Likely cause (hypothesis):
- What changed recently:
- Why the existing gates did not catch it:

## Mitigation plan

- Immediate containment:
- Rollback plan (if needed):
- Short-term fix:
- Owner:

## Post-incident actions

- Add or adjust verification gates:
- Add regression test(s):
- Update documentation / runbook:
- Follow-up issue(s):

## Notes

- Keep this short. If the incident expands, move details to a dedicated issue or report.
