# Guarded Automation Template

Purpose: Define what automation may do, and where humans must decide, for AI-assisted changes.

## Scope
- Applies to PRs created by LLM/agent workflows.
- This template is a policy stub; teams can extend it per repository.

## Allowed automation (safe)
- Drafting specs / blueprints
- Generating code and tests
- Running CI in verify-lite mode
- Posting summaries (PR summary, artifacts, links)

## Required human steps (non-automated)
- Approve merge after reviewing diffs and evidence
- Accept or reject risky changes (security, data, infra)
- Sign off on threshold changes (coverage/perf/a11y)

## Evidence required before merge
- PR summary with verification results
- Links to artifacts (reports, traces, trends)
- Rollback plan if behavior changes

## Gate policy (minimum)
- Verify Lite must be green
- Copilot review gate must be satisfied
- Any required label-gates must be satisfied

## Exception handling
- If a required gate cannot run, document why and open a follow-up issue
- Emergency fixes still require post-merge review and retroactive evidence

## Decision record (copy into PR comment)
```
Guarded Automation Decision
- Automation scope: [OK/Needs work]
- Human review: [OK/Needs work]
- Evidence: [OK/Needs work]
- Exceptions: [None/Describe]
- Notes:
```

## References
- `docs/quality/llm-first-review-checklist.md`
- `docs/quality/pr-summary-template.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/label-gating.md`
