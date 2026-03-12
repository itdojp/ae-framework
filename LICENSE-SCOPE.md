# License Scope

As of 2026-03-13, the repository-wide standard license remains the MIT License defined in `LICENSE`.

This document records scope-management rules for first-party, conditional, and excluded assets. It does not by itself change the effective license of any file.

## Current baseline

- Repository standard license: MIT (`LICENSE`)
- Proposed Apache-2.0 migration: tracked in `Issue #2623`
- Factual scope audit: `artifacts/reference/legal/license-scope-audit.json`

## First-party scope

Unless a sub-tree or file declares different terms, the repository-standard license applies to the first-party assets listed below.

- `.ae/**`
- `.devcontainer/**`
- `.github/**`
- `api/**`
- `apps/**`
- `benchmarks/**`
- `codex/**`
- `config/**`
- `configs/**`
- `contracts/**`
- `docker/**`
- `docs/**`
- `examples/**`
- `infra/**`
- `observability/**`
- `packages/**`
- `plans/**`
- `podman/**`
- `policies/**`
- `policy/**`
- `presets/**`
- `proofs/**`
- `samples/**`
- `schema/**`
- `scripts/**`
- `security/**`
- `spec/**`
- `src/**`
- `templates/**`
- `tests/**`
- `types/**`

Root files governed as first-party are inventoried by `scripts/legal/inventory-license-scope.mjs`.

## Conditional scope

The following paths are not treated as first-party by default. They require provenance review before any repository-standard license is asserted.

- `artifacts/**`
- `fixtures/**`
- `test-cassettes/**`

## Excluded from repository-standard licensing

The repository-standard software license does not grant rights to the following categories.

- Trademarks, service marks, logos, icons, product names, and brand assets
- Third-party, upstream, or vendored assets
- Any file or subtree that carries its own `LICENSE*`, `NOTICE*`, `COPYING*`, or explicit per-file header

## Operating rule

When scope questions arise, determine the status in this order:

1. File-local or subtree-local license/notice
2. Third-party/upstream provenance
3. Conditional inventory review
4. Repository-standard license

## Related documents

- `LICENSE`
- `TRADEMARKS.md`
- `THIRD_PARTY_NOTICES.md`
- `docs/project/LICENSE-MIGRATION-AUDIT.md`
