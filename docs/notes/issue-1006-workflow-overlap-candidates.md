# Issue 1006: Workflow Overlap Candidates (Phase 1.5 draft)

## Snapshot
- Commit: 61f30b60
- Source: docs/notes/issue-1006-workflow-inventory.md

## Overlap candidates (by naming proximity)

### CI / verification core
- ci.yml / ci-core.yml / ci-fast.yml / ci-extended.yml / ae-ci.yml / minimal-pipeline.yml / hermetic-ci.yml / pr-verify.yml / verify-lite.yml / verify.yml
  - Candidate: clarify required vs optional vs experimental pipelines.

### Spec / artifact validation
- spec-check.yml / spec-validation.yml / fail-fast-spec-validation.yml / validate-artifacts-ajv.yml / spec-generate-model.yml / codegen-drift-check.yml / generate-artifacts-preview.yml
  - Candidate: unify schema/artifact validation into a single gating entry point.

### Formal verification
- formal-verify.yml / formal-aggregate.yml / model-checking-manual.yml
  - Candidate: define a single formal "entry" and document when manual vs automated runs apply.

### Flake and stability
- flake-detect.yml / flake-maintenance.yml / nightly-monitoring.yml / parallel-test-execution.yml
  - Candidate: consolidate flake-related reporting artifacts and reduce duplicated scheduling.

### Release
- release.yml / release-quality-artifacts.yml
  - Candidate: confirm whether both are needed or can be chained in one workflow.

### Agent automation
- agent-commands.yml / agent-slash-commands.yml
  - Candidate: merge slash command routing if triggers overlap.

### Security / compliance
- security.yml / sbom-generation.yml / cedar-quality-gates.yml
  - Candidate: map which are required for PR gating vs nightly audit.

#### Trigger mapping (security/compliance group)
- security.yml: pull_request (branches: main; paths-ignore: docs/**, **/*.md; jobs gated by label "run-security") + push (branches: main, develop; paths-ignore: docs/**, *.md; jobs gated by label "run-security") + schedule (cron: 20 5 * * 1 UTC) + workflow_dispatch
- sbom-generation.yml: pull_request (branches: main; paths: package.json, pnpm-lock.yaml, packages/**, apps/**, src/**; job gated by label "run-security") + push (branches: main, develop; paths-ignore: docs/**, *.md) + schedule (cron: 40 5 * * 1 UTC) + workflow_dispatch (input: include_vulnerabilities)
- cedar-quality-gates.yml: pull_request (job gated by labels "run-security" or "run-cedar", enforce with "enforce-security") + push (branch: main; tags: v*) + workflow_dispatch

### Misc utilities
- workflow-lint.yml / branch-protection-apply.yml / auto-labels.yml / pr-summary-comment.yml
  - Candidate: keep separate, but ensure they do not duplicate gating outputs.

## Next steps
- Map each candidate group to its actual trigger (PR gate, label-gate, nightly, manual).
- Identify 1-2 lowest-risk consolidation moves (docs-only or wiring reuse).
