# Issue 1006: Config Reference Map (Phase 2 draft)

## Snapshot
- Date: 2026-01-14
- Source: `rg` across repo

## Purpose
Track where candidate config files are referenced so relocation can update both code and docs.

## Reference map (candidates)

### configs/api-extractor.json (moved in PR #1534)
- `package.json` (files list includes `configs/api-extractor.json`)
- `artifacts/types-gate-ci-validation.md` (link/reference)

### configs/benchmark-config.json (moved in PR #1533)
- `src/cli/benchmark-cli.ts` (default `./configs/benchmark-config.json`)
- `docs/benchmark/README.md` (multiple examples)
- `docs/benchmark/req2run-environment-setup.md`
- `docs/reference/CLI-COMMANDS-REFERENCE.md`

### mcp-config.json
- No direct code references found via `rg`.
- Check runtime config lookup in scripts or deployment docs before moving.

### sample-config.json
- In progress: PR #1535 updates defaults to `configs/samples/sample-config.json`.
- `src/cli/conformance-cli.ts` (default currently `sample-config.json`)
- `package.json` (`conformance:sample` uses `samples/conformance/sample-config.json`)
- `docs/getting-started/SETUP.md`
- `docs/guides/USAGE.md`
- `docs/reference/CLI-COMMANDS-REFERENCE.md`
- Note: tests reference `all-sample-config.json` (not the same file).

### configs/stryker/stryker.conf.cjs (moved in PR #1537)
- `docs/ci/phase2-ci-hardening-outline.md` (mentioned)
- `docs/notes/mutation-coverage-plan.md`
- `docs/notes/pipeline-baseline.md`

### tsconfig.build.json
- `package.json` (`build` script)
- `src/commands/verify/run.ts` (fallback for verify)
- `docs/reference/CLI-COMMANDS-REFERENCE.md`
- `artifacts/recovery-verify.md`

### tsconfig.types.json
- `package.json` (`api:emit`, type extraction)
- `scripts/api/check-types.mjs`
- `artifacts/types-hardening-validation.md`

### tsconfig.verify.json
- `package.json` (`types:check`, type-coverage)
- `src/commands/verify/run.ts` (primary verify path)
- `docs/quality/type-coverage-policy.md`
- `docs/reference/CLI-COMMANDS-REFERENCE.md`
- `artifacts/verify.md`, `artifacts/types-gate-ci-validation.md`

### configs/vitest/vitest.workspace.ts (moved in PR #1538)
- `package.json` (`test:unit`, `test:int`, `test:perf`)
- `docs/ci/phase2-ci-hardening-outline.md`

## Notes
- Many references are in docs; relocations must update examples to avoid drift.
- Code references in `src/commands/verify/run.ts` are runtime-sensitive; relocating tsconfig files requires updating both the CLI flags and fallback logic.

## Next
- For each candidate move, update the referenced scripts/CLI defaults and docs in the same PR.
- Consider adding a temporary shim or alias path for one cycle.
