# Hermetic Test Container Plan (Phase 3)

## Goal
- Provide reproducible, containerized test runs for CI stability without expanding required PR checks.
- Keep the default PR path light; run containers via opt-in (`run-hermetic`) or schedule.

## Scope (Phase 3)
- **Current baseline**: unit tests in container (`scripts/docker/run-unit.sh`, `infra/podman/unit-compose.yml`).
- **Planned expansion**: integration / e2e / quality / flake suites.

## Assumptions (versions)
- Node.js >=20.11 <23 (see `package.json` engines)
- pnpm 10.x (see `package.json` packageManager)
- Podman 4.8+ and podman-plugins 1.7+ for local parity (see `docs/infra/container-runtime.md`)
- Docker Desktop fallback supported via `scripts/lib/container.sh`

## Execution model (proposed)
1. Host prefetch: `pnpm fetch --prefer-offline` to warm the PNPM store.
2. Container run: mount `AE_HOST_STORE` into the container and run suite-specific commands.
3. Hermetic flags: `CI=true`, `TZ=UTC`, `SOURCE_DATE_EPOCH` for deterministic output.
4. Artifacts: write results under `reports/` and `logs/` on the host.

## Planned implementation steps
1. Add compose files for integration/e2e/quality/flake (under `infra/podman/`).
2. Add `scripts/docker/run-*.sh` wrappers, mirroring the unit runner.
3. Add a CI job gated by `run-hermetic` (non-blocking until stabilized).
4. Upload container test artifacts and summaries in the hermetic workflow.

## Risks and mitigations
- **Runner compatibility**: GitHub-hosted runners lack Podman; use Docker fallback.
- **Playwright/browser dependencies**: start with `test:e2e` alias (`test:phase3.2:core`) and expand after browser install is standardized.
- **Volume permissions**: pre-create `reports/` and `logs/` on the host; use tmpfs for `/tmp`.

## Related
- `docs/infra/container-runtime.md`
- `scripts/docker/run-unit.sh`
- `infra/podman/unit-compose.yml`
- `docs/testing/parallel-execution-strategy.md`
