# Ownership & Adoption Sample Flow

Purpose: Provide a minimal end-to-end flow that teams can follow when adopting ae-framework for AI-assisted changes.

## Flow (minimal)

1) Context bundle
- Build a context bundle using `docs/guides/context-bundle.md`
- Validate required context with `docs/guides/context-vacuum-checklist.md`

2) Spec kit
- Draft a spec using the appropriate template:
  - feature: `docs/templates/spec-kit/feature-spec-kit.md`
  - bugfix: `docs/templates/spec-kit/bugfix-spec-kit.md`
  - refactor: `docs/templates/spec-kit/refactor-spec-kit.md`

3) Blueprint
- Create a blueprint from `docs/templates/blueprint/blueprint-template.md`
- Record ownership, risks, and rollback plan

4) Implementation + verify
- Implement changes and run Verify Lite as baseline
- Opt-in to heavy gates as needed via labels (`docs/ci/label-gating.md`)

5) Evidence
- Generate PR summary using `docs/quality/pr-summary-template.md`
- Attach artifacts / links per `docs/quality/pr-summary-tool.md`

6) Review
- Apply `docs/quality/llm-first-review-checklist.md`
- Enforce `docs/quality/guarded-automation-template.md`
- Confirm Ownership DoD: `docs/quality/ownership-dod.md`

## Expected artifacts
- Context bundle
- Spec (feature/bugfix/refactor)
- Blueprint (ownership + rollback)
- PR summary + links to verification artifacts

## Notes
- This flow assumes verify-then-merge with human approval.
- Keep evidence short and link to artifacts for details.
