# Issue #1006: Runner Interface Draft (Phase 1)

## Goal
- Define a minimal, consistent CLI interface for `scripts/<category>/run.mjs`.
- Keep migration reversible and avoid changing behavior before wiring aliases.

## Common CLI shape (draft)
```
node scripts/<category>/run.mjs --profile=<name> [--dry-run] [--list]
```

### Flags
- `--profile=<name>`: selects a named bundle (e.g. `ci-lite`, `ci-extended`, `quick`).
- `--list`: prints available profiles for the category.
- `--dry-run`: prints the resolved command list without executing.

### Exit codes
- `0`: success
- `2`: unknown profile
- `3`: invalid configuration
- `>0`: propagated from the executed command

## Profile naming guidance
- **test**: `ci`, `ci-lite`, `ci-extended`, `fast`, `int` (reserved integration profile; not yet wired in `script-alias-map.json`, planned for Phase 2)
- **quality**: `all`, `gates`, `policy` (policy is reserved for later phases)
- **verify**: `lite`, `conformance`, `formal` (formal is reserved for later phases)
- **flake**: `detect`, `quick`, `thorough` (thorough is reserved for later phases)
- **security**: `quick`, `full`, `audit` (full/audit are reserved for later phases)

## Alias map usage
- `scripts/admin/script-alias-map.json` is the source of truth for legacy → new mapping.
- Alias wiring should emit deprecation warnings until Phase 2.
  Note: Phase 1 only wires the profiles present in the alias map; reserved names above will be added in later phases.

## DoD (Phase 1)
- Runner interface doc published.
- Alias map JSON + mapping doc exist.
- No runtime changes yet (docs only).
