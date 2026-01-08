# CI Troubleshooting Guide (Quick)

Purpose: Provide a short, deterministic path to diagnose common CI failures.

## 1) Identify the failing job
- Link the job in the PR or CI run summary
- Record the exact command and environment variables

## 2) Classify the failure
- **Lint/Type**: check `verify-lite` summary
- **Tests**: use `docs/testing/flaky-test-triage.md`
- **Artifacts/Codegen**: confirm `generate-artifacts` output
- **Security**: check label gating (`run-security`) and fork limitations

## 3) Reproduce locally (minimal)
- `pnpm run verify:lite`
- `pnpm run test:ci:lite`

## 4) Mitigate safely
- Prefer label-gated heavy suites (`docs/ci/label-gating.md`)
- Use stable profile for baseline (`docs/ci/stable-profile.md`)
- Document the fix and add a follow-up issue if needed

## References
- `docs/ci/ci-baseline-checklist.md`
- `docs/testing/test-categorization.md`
- `docs/testing/flaky-test-triage.md`
