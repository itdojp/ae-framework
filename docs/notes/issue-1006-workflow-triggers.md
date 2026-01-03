# Issue 1006: Workflow Trigger Map (Phase 1.5 draft)

## Snapshot
- Commit: 61f30b60
- Total workflows: 47

## Trigger counts
- issue_comment: 2
- pull_request: 31
- push: 24
- release: 1
- schedule: 10
- workflow_call: 6
- workflow_dispatch: 27

## Trigger → workflow files

### issue_comment (2)
- agent-commands.yml
- agent-slash-commands.yml

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
- generate-artifacts-preview.yml
- grafana-dashboards.yml
- hermetic-ci.yml
- parallel-test-execution.yml
- phase6-validation.yml
- podman-smoke.yml
- pr-summary-comment.yml
- pr-verify.yml
- quality-gates-centralized.yml
- sbom-generation.yml
- security.yml
- spec-check.yml
- spec-generate-model.yml
- spec-validation.yml
- testing-ddd-scripts.yml
- validate-artifacts-ajv.yml
- verify-lite.yml
- verify.yml
- workflow-lint.yml

### push (24)
- ae-ci.yml
- cedar-quality-gates.yml
- ci-extended.yml
- ci-fast.yml
- ci.yml
- codegen-drift-check.yml
- coverage-check.yml
- fail-fast-spec-validation.yml
- formal-verify.yml
- hermetic-ci.yml
- parallel-test-execution.yml
- podman-smoke.yml
- pr-verify.yml
- quality-gates-centralized.yml
- release-quality-artifacts.yml
- release.yml
- sbom-generation.yml
- security.yml
- spec-validation.yml
- testing-ddd-scripts.yml
- verify-lite.yml
- verify.yml
- webapi-sample-ci.yml
- workflow-lint.yml

### release (1)
- release-quality-artifacts.yml

### schedule (10)
- ci-extended.yml
- ci.yml
- docker-tests.yml
- flake-detect.yml
- flake-maintenance.yml
- grafana-dashboards.yml
- nightly-monitoring.yml
- nightly.yml
- sbom-generation.yml
- security.yml

### workflow_call (6)
- ci-core.yml
- ci-fast.yml
- codegen-drift-check.yml
- fail-fast-spec-validation.yml
- quality-gates-centralized.yml
- spec-validation.yml

### workflow_dispatch (27)
- ae-ci.yml
- branch-protection-apply.yml
- cedar-quality-gates.yml
- ci-extended.yml
- ci-fast.yml
- ci.yml
- docker-tests.yml
- flake-detect.yml
- flake-maintenance.yml
- formal-aggregate.yml
- formal-verify.yml
- generate-artifacts-preview.yml
- grafana-dashboards.yml
- hermetic-ci.yml
- minimal-pipeline.yml
- model-checking-manual.yml
- mutation-quick.yml
- nightly-monitoring.yml
- nightly.yml
- podman-smoke.yml
- release-quality-artifacts.yml
- sbom-generation.yml
- security.yml
- spec-check.yml
- spec-generate-model.yml
- verify-lite.yml
- webapi-sample-ci.yml

## Notes
- Use this map to identify redundant PR gates vs scheduled audits.
- Next: group by CI profiles (fast/verify-lite/extended/security/formal) and confirm ownership.