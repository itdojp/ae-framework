# Issue 1006: Workflow Trigger Profiles (Phase 1.5 draft)

## Snapshot
- Commit: 6f9fce7b
- Total workflows: 46

## Trigger signatures

### pull_request (4)
- adapter-thresholds.yml
- auto-labels.yml
- phase6-validation.yml
- pr-summary-comment.yml

### pull_request, push (7)
- coverage-check.yml
- lean-proof.yml
- parallel-test-execution.yml
- pr-verify.yml
- testing-ddd-scripts.yml
- verify.yml
- workflow-lint.yml

### pull_request, push, workflow_dispatch (5)
- ae-ci.yml
- formal-verify.yml
- hermetic-ci.yml
- podman-smoke.yml
- verify-lite.yml

### schedule, workflow_dispatch (5)
- docker-tests.yml
- flake-detect.yml
- flake-maintenance.yml
- nightly-monitoring.yml
- nightly.yml

### pull_request, push, workflow_call (4)
- codegen-drift-check.yml
- fail-fast-spec-validation.yml
- spec-validation.yml
- quality-gates-centralized.yml

### pull_request, workflow_dispatch (5)
- cedar-quality-gates.yml
- copilot-review-gate.yml
- formal-aggregate.yml
- spec-check.yml
- spec-generate-model.yml

### workflow_dispatch (5)
- branch-protection-apply.yml
- minimal-pipeline.yml
- model-checking-manual.yml
- mutation-quick.yml
- webapi-sample-ci.yml

### pull_request, push, schedule, workflow_dispatch (3)
- ci-extended.yml
- sbom-generation.yml
- security.yml

### issue_comment (1)
- agent-commands.yml

### pull_request, push, workflow_call, workflow_dispatch (1)
- ci-fast.yml

### pull_request, schedule, workflow_dispatch (1)
- grafana-dashboards.yml

### push (1)
- release.yml

### release, workflow_dispatch (1)
- release-quality-artifacts.yml

### push, schedule, workflow_dispatch (1)
- ci.yml

### workflow_call (1)
- ci-core.yml

### workflow_call, workflow_dispatch (1)
- validate-artifacts-ajv.yml

## Notes
- Use this profile map to identify overused trigger combinations (e.g., pull_request+push) for consolidation.
- Next: map each profile to a CI purpose (gate vs audit vs manual).
