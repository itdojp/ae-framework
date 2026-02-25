# Doc Consistency Lint

## Purpose
`check:doc-consistency` now runs two validators:
- `scripts/docs/check-doc-consistency.mjs`
- `scripts/docs/check-ci-doc-index-consistency.mjs`

Together they validate that key onboarding/CI-index documents stay aligned with the implementation.

Checks:
- `pnpm run <script>` references exist in `package.json`.
- Local file/path references in markdown links and inline code resolve to real files/directories.
- `docs/README.md` / `docs/ci-policy.md` include the canonical CI operation links.
- CI reference sections in `docs/ci-policy.md` avoid duplicate entries.

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

Note:
- `--format json` または `--docs` 指定時は互換性のため `check-doc-consistency.mjs` のみを実行します。
- CI索引チェックを併せて実行する場合は `pnpm run check:ci-doc-index-consistency` を利用してください。

CI index only:
```bash
pnpm run check:ci-doc-index-consistency
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
