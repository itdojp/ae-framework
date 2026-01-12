# Issue 1006: Config Inventory (Phase 2 draft)

## Snapshot
- Date: 2026-01-12
- Scope: repo root config-like files (top-level)

## Inventory (root-level)

| File | Purpose (guess) | Move candidate | Notes |
| --- | --- | --- | --- |
| `.editorconfig` | Editor defaults | Keep | Tooling expects root.
| `ae-framework.yml` | Project config (pipeline/runtime) | Keep | Referenced from root by scripts/tools.
| `ae-framework-v2.yml` | Project config v2 | Keep | Same as above.
| `ae.config.ts` | AE core config | Keep | Root entry is conventional.
| `api-extractor.json` | API Extractor config | Candidate | Could move to `configs/` if refs are updated.
| `benchmark-config.json` | Benchmarks config | Candidate | Used by scripts; can be moved with path update.
| `eslint.config.js` | ESLint root config | Keep (short-term) | Already have `configs/eslint.config.js`; consolidate later.
| `issues.yaml` | Issue templates/data | Keep | GitHub expects root.
| `mcp-config.json` | MCP server config | Candidate | Depends on runtime lookup path.
| `pnpm-lock.yaml` | pnpm lockfile | Keep | Tooling expects root.
| `pnpm-workspace.yaml` | workspace config | Keep | Tooling expects root.
| `sample-config.json` | Sample config | Candidate | Could move to `configs/` or `samples/`.
| `stryker.conf.cjs` | Stryker root config | Candidate | Already have `configs/stryker*.js`.
| `tsconfig.json` | TS base config | Keep | Tooling expects root.
| `tsconfig.build.json` | TS build config | Candidate | Can move if `extends` paths updated.
| `tsconfig.types.json` | TS types config | Candidate | Same as above.
| `tsconfig.verify.json` | TS verify config | Candidate | Same as above.
| `vitest.config.ts` | Vitest root config | Keep (short-term) | Default lookup expects root.
| `vitest.workspace.ts` | Vitest workspace config | Candidate | Can move if `--config` is always passed.

## Notes
- "Keep" means root is required or convenient for default tool lookup.
- "Candidate" means relocation is possible if we update references and CI commands.
- Consolidation should be staged with alias/compat for a few cycles to avoid breakage.

## Next (Phase 2)
- Confirm actual lookup paths from scripts/CI before moving.
- Decide a stable `configs/` layout and update references gradually.
- Update Issue #1006 with the inventory and a move plan.
