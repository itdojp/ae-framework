# Doc Consistency Lint

## Purpose
`check:doc-consistency` runs the following validators:
- `scripts/docs/check-doc-consistency.mjs`
- `scripts/docs/check-ci-doc-index-consistency.mjs`
- `scripts/docs/check-runbook-command-blocks.mjs`
- `scripts/docs/check-doc-todo-markers.mjs`

Together they validate that onboarding + CI operation docs stay aligned with the implementation and remain executable as runbooks.

Checks:
- `pnpm run <script>` references exist in `package.json`.
- Local file/path references in markdown links and inline code resolve to real files/directories.
- `docs/README.md` から辿れる `docs/ci/*` / `docs/quality/*` の主要ドキュメントも既定スコープで検証する。
- `docs/README.md` / `docs/ci-policy.md` include the canonical CI operation links.
- CI reference sections in `docs/ci-policy.md` avoid duplicate entries.
- CI runbook の shell code block を `bash -n` で構文検証する。
- `docs/ci/*` の TODO/FIXME マーカーが Issue 参照付きであることを検証する（`TODO(#1234)` / `FIXME(#1234)`）。

Current default targets:
- Base: `../../README.md`, `../README.md`, Getting Started, User Manual, Integrations
- Dynamic discovery: `docs/README.md` に記載された `docs/ci/*` / `docs/quality/*` の markdown

Generated-report references:
- `artifacts/*` / `reports/*` は生成物参照として missing-path 判定を除外する。

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
- `--format json` または `--docs` 指定時は互換性のため `check-doc-consistency.mjs` のみを実行します（他の3 validator はスキップ）。
- CI索引チェックを併せて実行する場合は `pnpm run check:ci-doc-index-consistency` を利用してください。

CI index only:
```bash
pnpm run check:ci-doc-index-consistency
```

Runbook command blocks only:
```bash
pnpm run check:runbook-command-blocks
```

Doc TODO markers only:
```bash
pnpm run check:doc-todo-markers
```

## Exclusion Rules
The checker intentionally ignores:
- external URLs (`https://...`, `mailto:...`, etc.)
- heading anchors (`#...`)
- wildcard/glob style entries (`*`)
- template variables (`${...}`)
- extension-only tokens such as `.md`

If a new docs section needs additional exclusions, update `scripts/docs/check-doc-consistency.mjs` and add a unit test under `tests/unit/docs/`.

## CI Integration
`Verify Lite` runs the checker before docs-only detection so broken references are caught early even on markdown-only changes.
