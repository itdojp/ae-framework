# Public Types Sync Runbook

This runbook defines the reproducible steps to keep `api/public-types.d.ts` aligned with current implementation.

## Scope

- Snapshot source: `artifacts/types/**/*.d.ts`
- Published snapshot: `api/public-types.d.ts`
- Targeted sync sources (outside `api:emit` default include):
  - `src/agents/adapters/ui-ux-agent-adapter.ts`
  - `src/utils/enhanced-state-manager.ts`

## Commands

```bash
# 1) Emit baseline declarations from current tsconfig include
pnpm api:emit

# 2) Sync targeted declarations from implementation sources
pnpm api:sync-targets

# 3) Rebuild api/public-types.d.ts snapshot
pnpm api:snapshot
```

Or run the full sequence:

```bash
pnpm api:update
```

## Verification

```bash
# Compare current artifacts bundle with committed snapshot
pnpm api:check
```

`api:check` internally executes `api:sync-targets` after `api:emit`, so drift in
the targeted declarations is also validated during CI checks.

## Notes

- `configs/tsconfig/tsconfig.types.json` emits only a subset of source files.
- Target sync uses `configs/tsconfig/tsconfig.public-types-sync.json` (extends
  `tsconfig.types.json`) to keep compiler options aligned while adding path
  mapping for `@ae-framework/spec-compiler`.
