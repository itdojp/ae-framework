## Verification Checklist
- [ ] `ae verify` passed locally
- [ ] LLM Replay OK（no cassette diff）
- [ ] Bench delta < 5%（seeded）
- [ ] (optional) `ae qa:flake --times 10` reviewed

## Notes
- Artifacts are uploaded by CI (14 days retention).
- For flaky tests, attach failing seeds if any.