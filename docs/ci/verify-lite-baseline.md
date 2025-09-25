# Verify Lite Baseline

This document summarizes the Verify Lite baseline setup and how heavy jobs are gated.

## Baseline (always-on)
- Triggers: `pull_request`, `push` to `main`, `workflow_dispatch`
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

## Notes
- Verify Lite remains lightweight by default; heavy steps are opt-in.
- Path filters prevent default heavy runs on unrelated `push` events.
