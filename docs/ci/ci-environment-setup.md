# CI Environment Setup (Quick)

Purpose: Minimal environment notes to reproduce CI locally without heavy suites.

## Prerequisites
- Node.js (v22.x)
- pnpm via corepack (`corepack enable`)
- Container runtime: Podman or Docker

## Recommended defaults
- pnpm store: `.pnpm-store` in repo root
- Use Verify Lite for baseline: `pnpm run verify:lite`
- Use CI-lite test suite: `pnpm run test:ci:lite`

## Container runtime notes
- Podman setup: `docs/infra/podman-shared-runner.md`
- Container runtime basics: `docs/infra/container-runtime.md`

## CI gating notes
- Heavy suites are label-gated (`docs/ci/label-gating.md`)
- Stable profile for baseline signal (`docs/ci/stable-profile.md`)

## Troubleshooting
- CI failures: `docs/ci/ci-troubleshooting-guide.md`
- Flaky tests: `docs/testing/flaky-test-triage.md`
