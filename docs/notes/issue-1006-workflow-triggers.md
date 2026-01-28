# Issue 1006: Workflow Trigger Map (Phase 1.5 draft)

## Snapshot
- Commit: worktree
- Generated: 2026-01-28 (manual)
- Total workflows: 44

## Trigger counts
- issue_comment: 1
- pull_request: 20
- pull_request_review: 1
- push: 13
- schedule: 7
- workflow_call: 20
- workflow_dispatch: 30
- workflow_run: 1

## Trigger → workflow files

### issue_comment (1)
- agent-commands.yml

### pull_request (20)
- adapter-thresholds.yml
- cedar-quality-gates.yml
- ci.yml
- codegen-drift-check.yml
- copilot-review-gate.yml
- coverage-check.yml
- formal-verify.yml
- grafana-dashboards.yml
- lean-proof.yml
- phase6-validation.yml
- pr-ci-status-comment.yml
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

### push (13)
- ci.yml
- codegen-drift-check.yml
- coverage-check.yml
- lean-proof.yml
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

### workflow_call (20)
- ae-ci.yml
- ci-core.yml
- ci-extended.yml
- ci-fast.yml
- ci.yml
- codegen-drift-check.yml
- fail-fast-spec-validation.yml
- flake-stability.yml
- formal-aggregate.yml
- parallel-test-execution.yml
- podman-smoke.yml
- hermetic-ci.yml
- pr-verify.yml
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
- pr-verify.yml
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
