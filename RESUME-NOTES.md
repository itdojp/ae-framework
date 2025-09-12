# RESUME Notes

Fill this before upgrade/handoff to ensure smooth resume.

## Current Task and Next Actions
- Context: CodeX upgrade; repo was in merge-conflict state. Conflicts resolved for codegen/tests/docs; build/test need follow-up due to stricter TS settings and type changes.
- Last command run: `pnpm verify:model`
- Next step to execute: `pnpm types:check` → fix top errors (spec-compiler type-only imports, exactOptionalPropertyTypes) → `pnpm build` → `pnpm test:fast`
- Blocking issues / TODOs:
  - Many TS errors from stricter tsconfig (verbatimModuleSyntax, exactOptionalPropertyTypes)
  - Benchmark/infra types out of sync (enums, ExecutionEnvironment shape)
  - Alloy specs report failures in model-check (logs under artifacts/codex)

## Environment
- Node: v22.0.0
- Package manager: pnpm 10.0.0 / npm 10.5.1
- Codex/AE tools version: local workspace
- Required env vars and secrets: none for build/test. Optional: `ALLOY_JAR` for Alloy headless run.

## Services and Ports
- Local services to start: none for unit tests
- Start commands: `pnpm dev` (optional demo servers)
- Ports used: N/A

## Key Commands
- Build: `pnpm build`
- Test (fast): `pnpm test:fast`
- Test (full): `pnpm test`
- Generate (code/tests/spec): `pnpm codex:generate:tests -- --use-operation-id --with-input`
- Formal checks: `pnpm verify:model`

## Artifacts and Reports
- Artifacts dir(s): `artifacts/codex`, `reports/benchmark`
- Coverage/report locations: test reporters as configured
- Last artifacts snapshot: `artifacts/handoff/` (see archived set)

## Notes
- Known flaky tests or workarounds: resilience/backoff tests can surface unhandled rejection noise; run individually when debugging
- Important links or docs: `docs/integrations/CODEX-INTEGRATION.md`, `docs/verify/FORMAL-CHECKS.md`
