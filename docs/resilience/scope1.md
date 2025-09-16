# Resilience Scope 1 — Baseline Verification

Purpose
- Ensure resilience primitives (retry/backoff, circuit breaker, bulkhead, timeout, rate limit) build and type-check cleanly.
- Keep CI stable: Verify Lite required; heavier tests remain opt-in via labels.

How to run (PR)
- Verify Lite: comment `/verify-lite`
- Optional batches (CI Fast):
  - `/qa-batch-cli` then `/ci-fast-dispatch`
  - `/qa-batch-property` or `/qa-batch-agents` similarly

Notes
- Scope 1 is a no-behavior-change verification. Follow-up scopes (A/B/C) can incrementally adjust types, utils/tests, and suite coverage as small PRs.
