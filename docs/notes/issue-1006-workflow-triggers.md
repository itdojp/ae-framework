# Issue 1006: Workflow Trigger Map (Phase 1.5 draft)

## Snapshot
- Commit: worktree (post flake schedule consolidation)
- Total workflows: 53

## Trigger counts
- issue_comment: 1
- pull_request: 31
- pull_request_review: 1
- push: 19
- release: 1
- schedule: 12
- workflow_call: 9
- workflow_dispatch: 34
- workflow_run: 1

## Trigger → workflow files

### issue_comment (1)
- agent-commands.yml

### pull_request (31)
- adapter-thresholds.yml
- ae-ci.yml
- auto-labels.yml
- cedar-quality-gates.yml
- ci-extended.yml
- ci-fast.yml
- codegen-drift-check.yml
- copilot-review-gate.yml
- coverage-check.yml
- fail-fast-spec-validation.yml
- formal-aggregate.yml
- formal-verify.yml
- grafana-dashboards.yml
- hermetic-ci.yml
- lean-proof.yml
- parallel-test-execution.yml
- phase6-validation.yml
- podman-smoke.yml
- pr-auto-update-branch.yml
- pr-summary-comment.yml
- pr-verify.yml
- quality-gates-centralized.yml
- sbom-generation.yml
- security.yml
- spec-check.yml
- spec-generate-model.yml
- spec-validation.yml
- testing-ddd-scripts.yml
- verify-lite.yml
- verify.yml
- workflow-lint.yml

### pull_request_review (1)
- copilot-review-gate.yml

### push (19)
- ae-ci.yml
- ci-extended.yml
- ci-fast.yml
- codegen-drift-check.yml
- coverage-check.yml
- fail-fast-spec-validation.yml
- hermetic-ci.yml
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

### release (1)
- release-quality-artifacts.yml

### schedule (12)
- auto-merge-enable.yml
- ci-extended.yml
- ci.yml
- docker-tests.yml
- flake-detect.yml
- flake-retry-dispatch.yml
- grafana-dashboards.yml
- nightly-monitoring.yml
- nightly.yml
- pr-ci-status-comment.yml
- sbom-generation.yml
- security.yml

### workflow_call (9)
- ci-core.yml
- ci-fast.yml
- codegen-drift-check.yml
- fail-fast-spec-validation.yml
- flake-stability.yml
- quality-gates-centralized.yml
- spec-validation.yml
- validate-artifacts-ajv.yml
- verify.yml

### workflow_dispatch (34)
- ae-ci.yml
- auto-merge-eligible.yml
- auto-merge-enable.yml
- branch-protection-apply.yml
- cedar-quality-gates.yml
- ci-extended.yml
- ci-fast.yml
- ci.yml
- copilot-review-gate.yml
- coverage-check.yml
- docker-tests.yml
- flake-detect.yml
- flake-retry-dispatch.yml
- formal-aggregate.yml
- formal-verify.yml
- grafana-dashboards.yml
- hermetic-ci.yml
- minimal-pipeline.yml
- model-checking-manual.yml
- mutation-quick.yml
- nightly-monitoring.yml
- nightly.yml
- parallel-test-coordinator.yml
- podman-smoke.yml
- pr-auto-update-branch.yml
- pr-ci-status-comment.yml
- release-quality-artifacts.yml
- sbom-generation.yml
- security.yml
- spec-check.yml
- spec-generate-model.yml
- validate-artifacts-ajv.yml
- verify-lite.yml
- webapi-sample-ci.yml

### workflow_run (1)
- ci-auto-rerun-failed.yml

## Notes
- Use this map to identify redundant PR gates vs scheduled audits.
- Next: group by CI profiles (fast/verify-lite/extended/security/formal) and confirm ownership.
