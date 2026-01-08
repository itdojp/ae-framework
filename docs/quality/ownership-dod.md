# Ownership DoD (Definition of Done)

Purpose: Define ownership requirements for AI-assisted changes so teams can explain, support, and roll back safely.

Scope:
- Applies to behavior changes, new integrations, or policy changes.
- Use alongside Spec/Blueprint and PR summary artifacts.

## Required ownership artifacts

- Owner: responsible person or team
- Runbook: operational steps for on-call and recovery
- Failure modes: known risks and expected mitigations
- Rollback plan: how to revert safely
- Evidence: PR summary, verification gates, and artifacts

## DoD checklist

- Owner is named and reachable
- Runbook exists or is updated
- Failure modes are listed and reviewed
- Rollback is documented and tested if practical
- PR evidence is complete (summary + artifacts)

## Suggested references
- `docs/quality/llm-first-review-checklist.md`
- `docs/quality/incident-triage-template.md`
- `docs/quality/pr-summary-template.md`
- `docs/templates/blueprint/blueprint-template.md`
