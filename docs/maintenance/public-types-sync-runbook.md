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

## Notes

- `configs/tsconfig/tsconfig.types.json` currently emits only a subset of source files.
- `api:sync-targets` keeps critical declarations synchronized even when those files are outside the default emit set.
