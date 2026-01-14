# Issue 1006: Config Inventory (Phase 2 draft)

## Snapshot
- Date: 2026-01-14
- Scope: repo root config-like files (top-level)

## Inventory (root-level)

| File | Purpose (guess) | Move candidate | Notes |
| --- | --- | --- | --- |
| `.editorconfig` | Editor defaults | Keep | Tooling expects root.
| `ae-framework.yml` | Project config (pipeline/runtime) | Keep | Referenced from root by scripts/tools.
| `ae-framework-v2.yml` | Project config v2 | Keep | Same as above.
| `ae.config.ts` | AE core config | Keep | Root entry is conventional.
| `eslint.config.js` | ESLint root config | Keep (short-term) | Already have `configs/eslint.config.js`; consolidate later.
| `issues.yaml` | Issue templates/data | Keep | GitHub expects root.
| `pnpm-lock.yaml` | pnpm lockfile | Keep | Tooling expects root.
| `pnpm-workspace.yaml` | workspace config | Keep | Tooling expects root.
| `sample-config.json` | Sample config | Moved | Relocated to `configs/samples/sample-config.json` (PR #1551).
| `tsconfig.json` | TS base config | Keep | Tooling expects root.
| `tsconfig.build.json` | TS build config | Moved | Relocated to `configs/tsconfig/tsconfig.build.json` (PR #1544).
| `tsconfig.types.json` | TS types config | Moved | Relocated to `configs/tsconfig/tsconfig.types.json` (PR #1545).
| `tsconfig.verify.json` | TS verify config | Moved | Relocated to `configs/tsconfig/tsconfig.verify.json` (PR #1547).
| `vitest.config.ts` | Vitest root config | Keep (short-term) | Default lookup expects root.

## Notes
- "Keep" means root is required or convenient for default tool lookup.
- "Candidate" means relocation is possible if we update references and CI commands.
- Consolidation should be staged with alias/compat for a few cycles to avoid breakage.

## Moved in Phase 2
- `configs/api-extractor.json` (PR #1534)
- `configs/benchmark-config.json` (PR #1533)
- `configs/stryker/stryker.conf.cjs` (PR #1537)
- `configs/vitest/vitest.workspace.ts` (PR #1538)
- `configs/mcp-config.json` (PR #1543)
- `configs/samples/sample-config.json` (PR #1551)
- `configs/samples/sample-context.json` (PR #1551)
- `configs/samples/sample-data.json` (PR #1551)
- `configs/samples/sample-rules.json` (PR #1551)
- `configs/tsconfig/tsconfig.build.json` (PR #1544)
- `configs/tsconfig/tsconfig.types.json` (PR #1545)
- `configs/tsconfig/tsconfig.verify.json` (PR #1547)

## Next (Phase 2)
- Confirm actual lookup paths from scripts/CI before moving.
- Decide a stable `configs/` layout and update references gradually.
- Update Issue #1006 with the inventory and a move plan.
