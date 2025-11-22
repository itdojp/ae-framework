Title: <concise change summary>

Summary
- What changed and why
- Risk/impact

CI Labels (optional)
- Add `run-qa` to execute QA/Bench on this PR
- Add `run-security` to execute Security/Compliance checks
- Add `ci-non-blocking` to allow non-critical checks to continue-on-error
- Add `coverage:<pct>` to set coverage threshold (default 80)
- For integration flake diagnostics, rerun the failing job with `AE_INTEGRATION_TRACE_HANDLES=1` (see `docs/testing/integration-runtime-helpers.md`)

Checklist
- [ ] Verify Lite passes locally (`pnpm types:check && pnpm lint && pnpm build`)
- [ ] test:fast passes (`pnpm run test:fast`)
- [ ] Docs updated if behavior changes (see `docs/ci-policy.md`)

If applicable (Web API + DB flow)
- [ ] Spec links記載: OpenAPI / BDD / Property
- [ ] 実行テストを列挙: lint / test:fast / test:integration / test:property / mutation quick(任意)
- [ ] キャッシュ操作を記載: sync-test-results (restore/store/snapshot) / trend比較結果
