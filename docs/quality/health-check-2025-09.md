# Repository Health Check — 2025-09-05

> 🌍 Language / 言語: English | 日本語

Scope: Types Gate, Verify, Bench, Flake, Branch Protection, and CI workflow hygiene.

## Current Gates & Policies
- PR Verify (pr-verify.yml)
  - CodeX quickstart runs in tolerant mode via env: `CODEX_SKIP_QUALITY=1`, `CODEX_TOLERANT=1`.
  - Summary/comments and artifacts are uploaded; job status remains green by design.
- Quality Gates (quality-gates-centralized.yml)
  - Triggered only on code changes via `paths` filters (`src/**`, `packages/**`, `apps/**`, `tests/**`, `configs/**`, `scripts/**`, `types/**`).
- SBOM (sbom-generation.yml)
  - Runs when manifests/code change; avoids docs-only PRs.
- Security (security.yml)
  - `paths-ignore` for docs/markdown to skip heavy scans on docs PRs.
  - Container scan steps guarded by `hashFiles('docker/Dockerfile')` at step level.
- Parallel Tests (parallel-test-execution.yml)
  - E2E job on PR runs only with label `run-e2e`; always runs on push.
  - Path filters identical to quality gates to reduce noise.
- Spec Validation
  - Reusable workflow is callable (`workflow_call`) and referenced by fail-fast pipelines.

## Lint & Hygiene
- actionlint: All workflows pass local `actionlint v1.7.1`.
- workflow reuse: Reusable workflows expose `workflow_call` and optional inputs.

## Types & Tests
- Type strict mode env available (`AE_TYPES_STRICT=1`).
- Stable CI test profile available: `pnpm run test:ci:stable` (excludes heavy system-integration tests). See `docs/ci/stable-profile.md`.

## Branch Protection (suggested)
- Require: actionlint, PR Verify, Quality Gates minimal, SBOM (manifests), Security (fast lanes), Spec Validation (if spec used).
- Optional: E2E label-gated job not required.

## Follow-ups
- Document additional exclusions for the stable profile as we identify flaky suites.
- Track CI duration metrics to refine path filters.
