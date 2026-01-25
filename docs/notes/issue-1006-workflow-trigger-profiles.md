# Issue 1006: Workflow Trigger Profiles (Phase 1.5 draft)

## Snapshot
- Commit: worktree (post nightly monitoring + flake retry + manual model-checking + parallel coordinator + pr auto-update + pr summary consolidation)
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

### pull_request, workflow_dispatch (5)
- cedar-quality-gates.yml
- formal-aggregate.yml
- formal-verify.yml
- spec-check.yml
- spec-generate-model.yml

### release, workflow_dispatch (1)
- release-quality-artifacts.yml

### schedule, workflow_dispatch (4)
- ci.yml
- docker-tests.yml
- flake-detect.yml
- nightly.yml

### workflow_call, workflow_dispatch (1)
- validate-artifacts-ajv.yml

### pull_request, pull_request_review, workflow_dispatch (1)
- copilot-review-gate.yml

### pull_request, push, workflow_call (5)
- codegen-drift-check.yml
- fail-fast-spec-validation.yml
- quality-gates-centralized.yml
- spec-validation.yml
- verify.yml

### pull_request, push, workflow_dispatch (6)
- ae-ci.yml
- coverage-check.yml
- hermetic-ci.yml
- parallel-test-execution.yml
- podman-smoke.yml
- verify-lite.yml

### pull_request, schedule, workflow_dispatch (2)
- grafana-dashboards.yml
- pr-ci-status-comment.yml

### pull_request, push, schedule, workflow_dispatch (3)
- ci-extended.yml
- sbom-generation.yml
- security.yml

### pull_request, push, workflow_call, workflow_dispatch (1)
- ci-fast.yml

## Notes
- Use this profile map to identify overused trigger combinations (e.g., pull_request+push) for consolidation.
- Next: map each profile to a CI purpose (gate vs audit vs manual).
