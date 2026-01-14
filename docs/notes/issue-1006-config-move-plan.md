# Issue 1006: Config Relocation Plan (Phase 2 draft)

## Snapshot
- Date: 2026-01-14
- Inputs: issue-1006-config-inventory.md

## Goals
- Reduce root-level config clutter while keeping tool defaults intact.
- Move only files that are safe to relocate with explicit path updates.
- Provide a staged migration so CI/local tooling does not break.

## Constraints
- Keep files that are required at repo root by default tooling.
- Prefer opt-in config paths (`--config`, `--project`, `--configFile`) before removal.
- Retain backward-compatible aliases for at least one release cycle.

## Proposed layout (target)

```
configs/
  api-extractor.json
  benchmark-config.json
  mcp-config.json
  samples/
    sample-config.json
  stryker/
    stryker.conf.cjs
  tsconfig/
    tsconfig.build.json
    tsconfig.types.json
    tsconfig.verify.json
  vitest/
    vitest.workspace.ts
```

## Candidate moves

| File | Proposed destination | Preconditions | Notes | Status |
| --- | --- | --- | --- | --- |
| api-extractor.json | configs/api-extractor.json | Update API Extractor invocation | Default path is root; must update scripts. | Done (PR #1534)
| benchmark-config.json | configs/benchmark-config.json | Update benchmark scripts | Ensure benchmark runner reads new path. | Done (PR #1533)
| mcp-config.json | configs/mcp-config.json | Update runtime lookup | Confirm where MCP server reads config. | Done (PR #1543)
| sample-config.json | configs/samples/sample-config.json | Update references | Could also move to `samples/`. | Done (PR #1535)
| stryker.conf.cjs | configs/stryker/stryker.conf.cjs | Update stryker command | Already have configs/stryker*.js; consolidate. | Done (PR #1537)
| tsconfig.build.json | configs/tsconfig/tsconfig.build.json | Update build scripts | Keep tsconfig.json at root. | Planned
| tsconfig.types.json | configs/tsconfig/tsconfig.types.json | Update scripts | Keep tsconfig.json at root. | Planned
| tsconfig.verify.json | configs/tsconfig/tsconfig.verify.json | Update scripts | Keep tsconfig.json at root. | Planned
| vitest.workspace.ts | configs/vitest/vitest.workspace.ts | Update test scripts | Vitest defaults to root; must pass config explicitly. | Done (PR #1538)

## Files to keep at root (for now)
- .editorconfig
- pnpm-lock.yaml
- pnpm-workspace.yaml
- tsconfig.json (base)
- vitest.config.ts (default lookup)
- eslint.config.js (until ESLint config consolidation)
- ae-framework.yml / ae-framework-v2.yml / ae.config.ts

## Migration steps (staged)

1) Add new locations and update scripts/CI to reference them.
2) Keep root-level shims (or small stub files) for one cycle if needed.
3) Update docs/notes and CI baseline references.
4) Remove root duplicates only after CI passes in two consecutive runs.

## Validation
- Run `pnpm run test:ci:lite` and `pnpm run verify-lite` after path updates.
- Ensure `pnpm run help` still lists valid scripts.

## Risks
- Tool default lookup can silently fall back to root (false green).
- CI-only commands may diverge from local runs if not updated together.

## Next actions
- Confirm actual lookup paths in scripts and workflows.
- Open PRs per file-group (1-3 files per PR) to keep changes reviewable.
