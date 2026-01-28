# Issue 1006: Workflow Trigger Profiles (Phase 1.5 draft)

## Snapshot
- Commit: worktree
- Generated: 2026-01-28 04:34:46 UTC
- Total workflows: 44

## Trigger signatures

### issue_comment (1)
- agent-commands.yml

### pull_request (3)
- adapter-thresholds.yml
- phase6-validation.yml
- pr-verify.yml

### push (1)
- release.yml

### workflow_call (2)
- ci-core.yml
- flake-stability.yml

### workflow_dispatch (4)
- branch-protection-apply.yml
- minimal-pipeline.yml
- mutation-quick.yml
- webapi-sample-ci.yml

### workflow_run (1)
- ci-auto-rerun-failed.yml

### pull_request, push (3)
- lean-proof.yml
- testing-ddd-scripts.yml
- workflow-lint.yml

### pull_request, workflow_dispatch (3)
- cedar-quality-gates.yml
- formal-verify.yml
- spec-generate-model.yml

### schedule, workflow_dispatch (3)
- docker-tests.yml
- flake-detect.yml
- nightly.yml

### workflow_call, workflow_dispatch (10)
- ci-extended.yml
- ci-fast.yml
- fail-fast-spec-validation.yml
- formal-aggregate.yml
- hermetic-ci.yml
- parallel-test-execution.yml
- podman-smoke.yml
- release-quality-artifacts.yml
- spec-check.yml
- validate-artifacts-ajv.yml

### pull_request, pull_request_review, workflow_dispatch (1)
- copilot-review-gate.yml

### pull_request, push, workflow_call (3)
- codegen-drift-check.yml
- quality-gates-centralized.yml
- verify.yml

### pull_request, push, workflow_dispatch (3)
- ae-ci.yml
- coverage-check.yml
- verify-lite.yml

### pull_request, schedule, workflow_dispatch (2)
- grafana-dashboards.yml
- pr-ci-status-comment.yml

### pull_request, push, schedule, workflow_dispatch (1)
- security.yml

### pull_request, push, schedule, workflow_call, workflow_dispatch (1)
- ci.yml

### pull_request, push, workflow_call, workflow_dispatch (2)
- sbom-generation.yml
- spec-validation.yml

## Notes
- Use this profile map to identify overused trigger combinations (e.g., pull_request+push) for consolidation.
- Next: map each profile to a CI purpose (gate vs audit vs manual).
