# Issue 1006: Workflow Overlap Candidates (Phase 1.5 draft)

## Snapshot
- Commit: 61f30b60
- Source: docs/notes/issue-1006-workflow-inventory.md

## Required checks snapshot (main protection)
- Date: 2026-01-14
- Required status checks:
  - `Verify Lite / verify-lite`
  - `Copilot Review Gate / gate`
- Note: Consolidation proposals must keep these checks intact (see docs/ci/branch-protection-operations.md).

## Overlap candidates (by naming proximity)

### CI / verification core
- ci.yml / ci-core.yml / ci-fast.yml / ci-extended.yml / ae-ci.yml / minimal-pipeline.yml / hermetic-ci.yml / pr-verify.yml / verify-lite.yml / verify.yml
  - Candidate: clarify required vs optional vs experimental pipelines.

### Spec / artifact validation
- spec-check.yml / spec-validation.yml / fail-fast-spec-validation.yml / validate-artifacts-ajv.yml / spec-generate-model.yml / codegen-drift-check.yml / generate-artifacts-preview.yml
  - Candidate: unify schema/artifact validation into a single gating entry point.

#### Trigger mapping (spec/artifact validation group)
- spec-check.yml: pull_request (paths: specs/formal/**, scripts/formal/verify-tla.mjs, package.json, .github/workflows/spec-check.yml) + workflow_dispatch
- spec-validation.yml: pull_request (paths: spec/**, .ae/**, docs/**) + push (main, develop; same paths) + workflow_call
- fail-fast-spec-validation.yml: pull_request (paths: spec/**, .ae/**) + push (main; no path filter) + workflow_call
- validate-artifacts-ajv.yml: pull_request (all PRs; strictness gated by label "enforce-artifacts")
- spec-generate-model.yml: pull_request (paths: specs/**, templates/**, scripts/**, docs/**, tests/**, artifacts/**, .github/workflows/spec-generate-model.yml) + workflow_dispatch
- codegen-drift-check.yml: pull_request (all PRs to main; execution gated by label "run-drift") + push (main; paths: spec/**/*.md, .ae/ae-ir.json, src/codegen/**, templates/**, .github/workflows/codegen-drift-check.yml) + workflow_call
- generate-artifacts-preview.yml: pull_request (paths: specs/**, templates/**, scripts/**, docs/**, tests/**, artifacts/**, .github/workflows/generate-artifacts-preview.yml) + workflow_dispatch

### Formal verification
- formal-verify.yml / formal-aggregate.yml / model-checking-manual.yml
  - Candidate: define a single formal "entry" and document when manual vs automated runs apply.

#### Trigger mapping (formal verification group)
- formal-verify.yml: pull_request (types: opened, synchronize, reopened, ready_for_review, labeled; jobs gated by label "run-formal") + push (tags: v*) + workflow_dispatch (inputs.target)
- formal-aggregate.yml: pull_request (types: opened, synchronize, reopened, labeled; job gated by label "run-formal") + workflow_dispatch
- model-checking-manual.yml: workflow_dispatch (inputs.engine, spec_path)

### Flake and stability
- flake-detect.yml / flake-maintenance.yml / nightly-monitoring.yml / parallel-test-execution.yml
  - Candidate: consolidate flake-related reporting artifacts and reduce duplicated scheduling.

#### Trigger mapping (flake/stability group)
- flake-detect.yml: schedule (cron: 0 21 * * * UTC) + workflow_dispatch
- flake-maintenance.yml: schedule (cron: 0 10 * * * UTC) + workflow_dispatch
- nightly-monitoring.yml: schedule (cron: 15 19 * * * UTC) + workflow_dispatch
- parallel-test-execution.yml: pull_request (branches: main; paths: src/**, packages/**, apps/**, tests/**, configs/**, scripts/**, types/**) + push (branches: main, develop)

### Release
- release.yml / release-quality-artifacts.yml
  - Candidate: confirm whether both are needed or can be chained in one workflow.

#### Trigger mapping (release group)
- release.yml: push (tags: v*)
- release-quality-artifacts.yml: release (published) + push (tags: v*) + workflow_dispatch

### Agent automation
- agent-commands.yml / agent-slash-commands.yml
  - Candidate: merge slash command routing if triggers overlap.

### Security / compliance
- security.yml / sbom-generation.yml / cedar-quality-gates.yml
  - Candidate: map which are required for PR gating vs nightly audit.

### Misc utilities
- workflow-lint.yml / branch-protection-apply.yml / auto-labels.yml / pr-summary-comment.yml
  - Candidate: keep separate, but ensure they do not duplicate gating outputs.

## Next steps
- Map each candidate group to its actual trigger (PR gate, label-gate, nightly, manual).
- Identify 1-2 lowest-risk consolidation moves (docs-only or wiring reuse).

## Phase 2 shortlist (low-risk consolidation)
These are proposals to reduce overlap without changing required checks or safety gates. Execute after confirming triggers and required status checks.

1) Spec / artifact validation
   - Treat `spec-validation.yml` as the canonical PR gate.
   - Fold `validate-artifacts-ajv.yml` into `spec-validation.yml` or call it via a reusable workflow.
   - Keep `fail-fast-spec-validation.yml` as an alias only if the PR gate cannot be updated safely.

2) Artifact preview vs generation
   - Clarify the role split between `generate-artifacts-preview.yml` and `spec-generate-model.yml`.
   - Option: move the preview step into `spec-generate-model.yml` as a separate job and remove duplication.

3) Agent command routing
   - If `agent-commands.yml` and `agent-slash-commands.yml` share triggers, merge into a single workflow with separate jobs.

## Readiness checklist
- Confirm which workflows are required by branch protection.
- Confirm whether any workflow is used by external automation or documentation.
- Verify that consolidated workflows still publish the same summary comments/artifacts.
