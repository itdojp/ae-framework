# Issue 1006: Workflow Trigger Map (Phase 1.5 draft)

## Snapshot
- Commit: worktree
- Generated: 2026-01-28 01:25:38 UTC
- Total workflows: 44

## Trigger counts
- issue_comment: 1
- pull_request: 24
- pull_request_review: 1
- push: 16
- schedule: 7
- workflow_call: 16
- workflow_dispatch: 30
- workflow_run: 1

## Trigger → workflow files

### issue_comment (1)
- agent-commands.yml

### pull_request (24)
- adapter-thresholds.yml
- ae-ci.yml
- cedar-quality-gates.yml
- ci.yml
- codegen-drift-check.yml
- copilot-review-gate.yml
- coverage-check.yml
- formal-verify.yml
- grafana-dashboards.yml
- lean-proof.yml
- parallel-test-execution.yml
- phase6-validation.yml
- podman-smoke.yml
- pr-ci-status-comment.yml
- pr-verify.yml
- quality-gates-centralized.yml
- sbom-generation.yml
- security.yml
- spec-generate-model.yml
- spec-validation.yml
- testing-ddd-scripts.yml
- verify-lite.yml
- verify.yml
- workflow-lint.yml

### pull_request_review (1)
- copilot-review-gate.yml

### push (16)
- ae-ci.yml
- ci.yml
- codegen-drift-check.yml
- coverage-check.yml
- lean-proof.yml
- parallel-test-execution.yml
- podman-smoke.yml
- quality-gates-centralized.yml
- release.yml
- sbom-generation.yml
- security.yml
- spec-validation.yml
- testing-ddd-scripts.yml
- verify-lite.yml
- verify.yml
- workflow-lint.yml

### schedule (7)
- ci.yml
- docker-tests.yml
- flake-detect.yml
- grafana-dashboards.yml
- nightly.yml
- pr-ci-status-comment.yml
- security.yml

### workflow_call (16)
- ci-core.yml
- ci-extended.yml
- ci-fast.yml
- ci.yml
- codegen-drift-check.yml
- fail-fast-spec-validation.yml
- flake-stability.yml
- formal-aggregate.yml
- hermetic-ci.yml
- quality-gates-centralized.yml
- release-quality-artifacts.yml
- sbom-generation.yml
- spec-check.yml
- spec-validation.yml
- validate-artifacts-ajv.yml
- verify.yml

### workflow_dispatch (30)
- ae-ci.yml
- branch-protection-apply.yml
- cedar-quality-gates.yml
- ci-extended.yml
- ci-fast.yml
- ci.yml
- copilot-review-gate.yml
- coverage-check.yml
- docker-tests.yml
- fail-fast-spec-validation.yml
- flake-detect.yml
- formal-aggregate.yml
- formal-verify.yml
- grafana-dashboards.yml
- hermetic-ci.yml
- minimal-pipeline.yml
- mutation-quick.yml
- nightly.yml
- parallel-test-execution.yml
- podman-smoke.yml
- pr-ci-status-comment.yml
- release-quality-artifacts.yml
- sbom-generation.yml
- security.yml
- spec-check.yml
- spec-generate-model.yml
- spec-validation.yml
- validate-artifacts-ajv.yml
- verify-lite.yml
- webapi-sample-ci.yml

### workflow_run (1)
- ci-auto-rerun-failed.yml

## Notes
- Use this map to identify redundant PR gates vs scheduled audits.
- Next: group by CI profiles (fast/verify-lite/extended/security/formal) and confirm ownership.
