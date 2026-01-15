# Issue 1006: Workflow Overlap Candidates (Phase 1.5 draft)

## Snapshot
- Commit: 6f9fce7b
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
- spec-check.yml / spec-validation.yml / fail-fast-spec-validation.yml / validate-artifacts-ajv.yml / spec-generate-model.yml / codegen-drift-check.yml
  - Candidate: unify schema/artifact validation into a single gating entry point.

#### Trigger mapping (spec/artifact validation group)
- spec-check.yml: pull_request (paths: specs/formal/**, scripts/formal/verify-tla.mjs, package.json, .github/workflows/spec-check.yml) + workflow_dispatch
- spec-validation.yml: pull_request (paths: spec/**, .ae/**, artifacts/**, schema/**, docs/schemas/**, specs/formal/**, .github/workflows/spec-validation.yml, .github/workflows/validate-artifacts-ajv.yml) + push (main, develop; same paths) + workflow_call
- fail-fast-spec-validation.yml: pull_request (paths: spec/**, .ae/**) + push (main; no path filter) + workflow_call
- validate-artifacts-ajv.yml: workflow_call (invoked from spec-validation on PRs) + workflow_dispatch
- spec-generate-model.yml: pull_request (paths: specs/**, templates/**, scripts/**, tests/**, artifacts/**, .github/workflows/spec-generate-model.yml) + workflow_dispatch
- codegen-drift-check.yml: pull_request (all PRs to main; types: opened, synchronize, reopened, labeled; paths-ignore: docs/**, **/*.md; execution gated by label "run-drift") + push (main; paths: spec/**/*.md, .ae/ae-ir.json, src/codegen/**, templates/**, .github/workflows/codegen-drift-check.yml) + workflow_call

### Formal verification
- formal-verify.yml / formal-aggregate.yml / model-checking-manual.yml / lean-proof.yml
  - Candidate: define a single formal "entry" and document when manual vs automated runs apply.

#### Trigger mapping (formal verification group)
- formal-verify.yml: pull_request (types: opened, synchronize, reopened, ready_for_review, labeled; paths-ignore: docs/**, **/*.md; jobs gated by label "run-formal") + push (tags: v*) + workflow_dispatch (inputs.target)
- formal-aggregate.yml: pull_request (types: opened, synchronize, reopened, labeled; paths-ignore: docs/**, **/*.md; job gated by label "run-formal") + workflow_dispatch
- model-checking-manual.yml: workflow_dispatch (inputs.engine, spec_path)
- lean-proof.yml: pull_request (paths: proofs/lean/**, .github/workflows/lean-proof.yml) + push (main; same paths)

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
- release-quality-artifacts.yml: release (published) + workflow_dispatch

### Agent automation
- agent-commands.yml
  - Consolidate PR/Issue slash command routing into a single workflow.

#### Trigger mapping (agent automation group)
- agent-commands.yml: issue_comment (types: created; job for PR comments + job for issue comments)

### Security / compliance
- security.yml / sbom-generation.yml / cedar-quality-gates.yml
  - Candidate: map which are required for PR gating vs nightly audit.

#### Trigger mapping (security/compliance group)
- security.yml: pull_request (branches: main; paths-ignore: docs/**, **/*.md; jobs gated by label "run-security") + push (branches: main, develop; paths-ignore: docs/**, **/*.md; jobs run unconditionally) + schedule (cron: 20 5 * * 1 UTC) + workflow_dispatch
- sbom-generation.yml: pull_request (branches: main; paths: package.json, pnpm-lock.yaml, packages/**, apps/**, src/**; job gated by label "run-security") + push (branches: main, develop; paths-ignore: docs/**, **/*.md; job runs unconditionally) + schedule (cron: 40 5 * * 1 UTC) + workflow_dispatch (input: include_vulnerabilities)
- cedar-quality-gates.yml: pull_request (job gated by labels "run-security" or "run-cedar"; enforce with "enforce-security") + push (branch: main; tags: v*) + workflow_dispatch (note: job is effectively skipped on push/dispatch because it depends on PR labels)

### Misc utilities
- workflow-lint.yml / branch-protection-apply.yml / auto-labels.yml / pr-summary-comment.yml
  - Candidate: keep separate, but ensure they do not duplicate gating outputs.

#### Trigger mapping (misc utilities group)
- workflow-lint.yml: pull_request (paths: .github/workflows/**) + push (branches: main, develop; paths: .github/workflows/**)
- branch-protection-apply.yml: workflow_dispatch (inputs: preset, branch)
- auto-labels.yml: pull_request (types: opened, edited, synchronize, reopened; paths-ignore: docs/**, *.md)
- pr-summary-comment.yml: pull_request (types: opened, synchronize, reopened; paths-ignore: docs/**, **/*.md)

## Next steps
- Map each candidate group to its actual trigger (PR gate, label-gate, nightly, manual).
- Identify 1-2 lowest-risk consolidation moves (docs-only or wiring reuse).

## Phase 2 shortlist (low-risk consolidation)
These are proposals to reduce overlap without changing required checks or safety gates. Execute after confirming triggers and required status checks.

1) Spec / artifact validation
   - ✅ Completed: `spec-validation.yml` をPRゲートとして採用し、`validate-artifacts-ajv.yml` を workflow_call で呼び出す構成に統合済み。
   - ✅ Completed: required checks への影響なしで統合を反映済み。

2) Artifact preview vs generation
   - ✅ Completed: preview step/comment を `spec-generate-model.yml` に集約し、重複していた `generate-artifacts-preview.yml` を削除。

3) Agent command routing
   - ✅ Completed: `agent-commands.yml` が PR/Issue の slash command をジョブ分岐で処理する構成に統合済み。

## Readiness checklist
- Confirm which workflows are required by branch protection.
- Confirm whether any workflow is used by external automation or documentation.
- Verify that consolidated workflows still publish the same summary comments/artifacts.
