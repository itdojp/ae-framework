# Verify Lite Baseline

This document summarizes the Verify Lite baseline setup and how heavy jobs are gated.

## Baseline (always-on)
- Triggers: `pull_request`, `push` to `main`, `workflow_dispatch`
- Re-runs on PR label changes (`pull_request.types` includes `labeled`)
- Concurrency: `verify-lite-${{ github.ref }}` with cancel-in-progress to avoid overlap
- Steps (minimal):
  - Type check: `pnpm types:check`
  - Lint (non-blocking): `pnpm lint || true`
  - Build: `pnpm run build`
  - Fast tests: `pnpm -s run test:fast`
  - Self-test (non-blocking): `scripts/ci/verify-lite-selftest.mjs`
- Label gates (PR only):
  - `run-formal`: enable formal stubs (non-blocking)
  - `run-resilience`: enable resilience quick tests (non-blocking)
- PR summary includes a small section listing the state of label gates.

## Heavy workflows (gated)
- SBOM/Security: label-gated on PR (`run-security`) and path-gated on `push` (manifests/code)
- ae-ci (QA/bench): label-gated on PR (`run-qa`) and path-gated on `push` (workspaces/code)

## Usage
- Re-dispatch Verify Lite on the PR head: comment `/verify-lite`
- Opt-in heavy checks via labels on PR:
  - `/run-formal`, `/run-security`, `/run-qa`

### Quick Ops
- Re-run Verify Lite fast: `/verify-lite`
- Enable formal steps in Verify Lite: add label `run-formal` (or comment `/run-formal`)
- Enable resilience quick tests: add label `run-resilience` (or comment `/run-resilience`)
- Enable QA/bench (ae-ci): add label `run-qa` (or comment `/run-qa`)
- Make coverage required for this PR: add label `enforce-coverage`; optionally set threshold via `coverage:<pct>`

## Notes
- Verify Lite remains lightweight by default; heavy steps are opt-in.
- Path filters prevent default heavy runs on unrelated `push` events.

## Local Checks (baseline)
Run these locally to approximate the Verify Lite baseline:

```bash
corepack enable && pnpm i && pnpm -s types:check && pnpm -s build && pnpm run test:fast
```
