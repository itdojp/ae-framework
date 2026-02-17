# Doc Consistency Lint

## Purpose
`scripts/docs/check-doc-consistency.mjs` validates that key onboarding documents stay aligned with the implementation.

Checks:
- `pnpm run <script>` references exist in `package.json`.
- Local file/path references in markdown links and inline code resolve to real files/directories.

Current default targets:
- `README.md`
- `docs/README.md`
- `docs/getting-started/QUICK-START-GUIDE.md`
- `docs/product/USER-MANUAL.md`
- `docs/integrations/QUICK-START-CODEX.md`

## Usage
```bash
pnpm run check:doc-consistency
```

JSON output:
```bash
pnpm run check:doc-consistency -- --format json
```

Custom files:
```bash
pnpm run check:doc-consistency -- --docs README.md,docs/README.md
```

## Exclusion Rules
The checker intentionally ignores:
- external URLs (`https://...`, `mailto:...`, etc.)
- heading anchors (`#...`)
- wildcard/glob style entries (`*`)
- template variables (`${...}`)
- non-path tokens (no slash)

If a new docs section needs additional exclusions, update `scripts/docs/check-doc-consistency.mjs` and add a unit test under `tests/unit/docs/`.

## CI Integration
`Verify Lite` runs the checker before docs-only detection so broken references are caught early even on markdown-only changes.
