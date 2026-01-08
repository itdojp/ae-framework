# Issue #1006: Script Migration Plan (2026-01-08)

## Goal
- Reduce script count and improve discoverability without breaking CI.
- Preserve existing entry points via aliases during transition.

## Inputs
- docs/notes/issue-1006-script-inventory.md
- docs/notes/issue-1006-workflow-*.md

## Strategy
1) Define top-level categories (core, quality, verify, ci, agents, formal, benchmark, tools).
   Note: The `agents` and `formal` categories are reserved for later phases and are included here to define the long-term category taxonomy.
2) For each category, create a single entry script under scripts/<category>/run.mjs (where `<category>` is a placeholder; for example, scripts/test/run.mjs).
3) Preserve existing scripts as aliases while emitting deprecation warnings.
4) Add pnpm run help to list new categories and recommended entry points.

## Phase 1 (Week 1-2)
- Focus categories (within the Strategy taxonomy): test, quality, verify, flake, security.
  Note: Phase 1 keeps finer-grained labels (test/flake/security) while they are mapped into the final top-level categories.
- For each category:
  - Identify the top 5 most used scripts.
  - Group them into run targets with flags.
  - Record a mapping table in docs/notes/issue-1006-script-mapping.md.
- Optional: add scripts/admin/script-alias-map.json to track the migration.

## Deprecation Policy
- Keep old script names for two releases.
- Print a warning when a deprecated script runs.
- Document the removal timeline and the new replacement.

## DoD
- Mapping table published for Phase 1 categories.
- CI uses the new entry points without failures.
- pnpm run help lists categories and the recommended entry points.
