# CI Labels Quick Reference

Use these labels to opt-in heavy jobs or adjust policies on PRs.

- run-formal: enable formal steps (Verify Lite/formal-verify); non-blocking
- run-resilience: enable resilience quick tests in Verify Lite; non-blocking
- run-qa: enable ae-ci QA/bench on PRs
- run-security: enable Security/SBOM on PRs
- run-drift: enable Codegen Drift Check on PRs
- run-cedar: enable Cedar policies validation (report-only)
- enforce-a11y: enforce adapter a11y thresholds (critical=0, serious=0)
- run-hermetic: enable Hermetic CI on PRs
- ci-non-blocking: run selected jobs with continue-on-error
- enforce-coverage: enforce coverage threshold (coverage-check)
- coverage:<pct>: override coverage threshold (e.g., coverage:75)
- enforce-typecov: enforce type coverage threshold (quality-gates)
- pr-summary:detailed: switch PR summary to detailed mode
- lang:ja: render PR summary in Japanese where supported

Notes
- Most of the above also cause workflows to re-run automatically (pull_request.types includes labeled).
- Many heavy workflows are path-gated on push to prevent default runs on unrelated changes.
