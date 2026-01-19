# Issue 1005: Automated Flake Recovery (Phase 3 Draft)

## Goal
Define a minimal, safe automation loop that retries flaky CI jobs once, records evidence, and avoids infinite retries.

## Scope (Phase 3)
- Target workflows: flake-detect, verify-lite, pr-verify (non-required jobs only).
- Trigger: schedule + workflow_dispatch only. No change to required checks.
- Output: job summary + artifact note (run ID, failed jobs, retry outcome).

## Proposed behavior
1) Detect failed jobs from the last run summary.
2) Retry failed jobs once (maxAttempts=1).
3) Post a concise status note to the PR (if applicable).
4) Stop if:
   - Retry already executed, or
   - Failure is non-retriable (infra label not present), or
   - Time budget exceeded (e.g., >15 min).

## Guardrails
- Do not rerun required checks automatically.
- Do not rerun when failure is deterministic (lint/type/schema errors).
- Use a marker in PR comments to avoid duplicate updates.

## Data captured
- Run ID / workflow name / commit SHA
- Failed job names and final status
- Retry decision (skipped / retried / blocked)

## Open questions
- Which workflows should emit the retry eligibility signal?
- Should retries be restricted to label-gated runs (run-flake)?

## Next steps
- Identify candidate workflows and add a retry eligibility flag in summaries.
- Add a lightweight dispatcher that reads the summary and calls rerun API.
- Validate behavior on a dry-run schedule.
