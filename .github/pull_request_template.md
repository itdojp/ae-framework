Title: <concise change summary>

Summary
- What changed and why
- Risk/impact

CI Labels (optional)
- Add `run-qa` to execute QA/Bench on this PR
- Add `run-security` to execute Security/Compliance checks
- Add `ci-non-blocking` to allow non-critical checks to continue-on-error
- Add `coverage:<pct>` to set coverage threshold (default 80)

Checklist
- [ ] Verify Lite passes locally (`pnpm types:check && pnpm lint && pnpm build`)
- [ ] test:fast passes (`pnpm run test:fast`)
- [ ] Docs updated if behavior changes (see `docs/ci-policy.md`)
