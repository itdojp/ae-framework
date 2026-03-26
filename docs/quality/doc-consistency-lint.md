---
docRole: derived
canonicalSource:
- docs/reference/DOC-GOVERNANCE.md
- scripts/docs/check-doc-consistency-all.mjs
lastVerified: '2026-03-26'
---
# Doc Consistency Lint

> Language / 言語: English | 日本語

---

## English

### Purpose
`check:doc-consistency` runs the following validators:
- `scripts/docs/check-doc-consistency.mjs`
- `scripts/docs/check-ci-doc-index-consistency.mjs`
- `scripts/docs/check-agent-commands-doc-sync.mjs`
- `scripts/docs/check-runbook-command-blocks.mjs`
- `scripts/docs/check-doc-todo-markers.mjs`
- `scripts/docs/check-contract-catalog-coverage.mjs`
- `scripts/docs/check-doc-governance.mjs`

Together they validate that onboarding + CI operation docs stay aligned with the implementation and remain executable as runbooks.

Checks:
- `pnpm run <script>` references exist in `package.json`.
- Local file/path references in markdown links and inline code resolve to real files/directories.
- In addition to the primary `docs/ci/*` and `docs/quality/*` documents linked from `docs/README.md`, the default scope also validates trust-tier front matter across `docs/TLA+/*`, `docs/adapters/*`, `docs/agent-builder/*`, `docs/agents/recipes/*`, `docs/architecture/*`, `docs/articles/*`, `docs/articles/zenn/*`, `docs/benchmark/*`, `docs/changes/*`, `docs/cheatsheets/*`, `docs/codex/*`, `docs/contributing/*`, `docs/ddd/*`, `docs/development/*`, `docs/examples/*`, `docs/flows/*`, `docs/getting-started/*`, `docs/guides/*`, `docs/handoff/*`, `docs/infra/*`, `docs/integrations/*`, `docs/internal/*`, `docs/legacy/**/*.md`, `docs/maintenance/*`, `docs/notes/*`, `docs/observability/*`, `docs/operate/*`, `docs/operations/*`, `docs/phases/*`, `docs/product/*`, `docs/project/*`, `docs/proposals/*`, `docs/reference/*`, `docs/research/*`, `docs/resilience/*`, `docs/roadmap/*`, `docs/samples/*`, `docs/spec/*`, `docs/strategy/*`, `docs/templates/**/*.md`, `docs/testing/*`, `docs/trace/*`, `docs/trace/grafana/*`, `docs/troubleshooting/*`, `docs/verify/*`, and `docs/workflows/*`.
- `docs/README.md` / `docs/ci-policy.md` include the canonical CI operation links.
- CI reference sections in `docs/ci-policy.md` avoid duplicate entries.
- `docs/agents/commands.md` stays synchronized with `.github/workflows/agent-commands.yml`.
- Shell code blocks in CI runbooks are syntax-checked with `bash -n`.
- TODO/FIXME markers under `docs/ci/*` require issue references such as `TODO(#<issue>)` or `FIXME(#<issue>)`.
- Governed docs must provide valid `docRole`, `canonicalSource`, and `lastVerified` front matter.
- `docs/legacy/**/*.md` and `docs/notes/*.md` are treated as archival / working-note narrative, so narrative warnings intentionally ignore historical wording and issue-memo language.

Current default targets:
- Base: the repository-root README file, `docs/README.md`, and the primary documents listed in `DEFAULT_DOC_FILES` such as the Getting Started, Product, and Integrations guides
- Dynamic discovery: use the repository-root README file and `docs/README.md` as seed files, then recursively add linked `docs/**/*.md` entries within the configured discovery prefixes

Generated-report references:
- `artifacts/*` / `reports/*` are treated as generated-report references and are excluded from missing-path failures.

### Usage
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
- When `--format json` or `--docs` is specified, only `check-doc-consistency.mjs` runs for compatibility; the other validators are skipped.
- Run `pnpm run check:ci-doc-index-consistency` separately when CI index validation is also required.

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

### Exclusion Rules
The checker intentionally ignores:
- external URLs (`https://...`, `mailto:...`, etc.)
- heading anchors (`#...`)
- wildcard/glob style entries (`*`)
- template variables (`${...}`)
- extension-only tokens such as `.md`

If a new docs section needs additional exclusions, update `scripts/docs/check-doc-consistency.mjs` and add a unit test under `tests/unit/docs/`.

### CI Integration
`Verify Lite` and `Docs Doctest` both invoke `check-doc-consistency-all.mjs`. This expands required-lane coverage beyond broken references to include contract catalog coverage and doc governance validation.

## 日本語

### 目的
`check:doc-consistency` は次の validator をまとめて実行します。
- `scripts/docs/check-doc-consistency.mjs`
- `scripts/docs/check-ci-doc-index-consistency.mjs`
- `scripts/docs/check-agent-commands-doc-sync.mjs`
- `scripts/docs/check-runbook-command-blocks.mjs`
- `scripts/docs/check-doc-todo-markers.mjs`
- `scripts/docs/check-contract-catalog-coverage.mjs`
- `scripts/docs/check-doc-governance.mjs`

これらをまとめて実行することで、オンボーディング文書と CI 運用文書が実装と整合し、runbook として実行可能な状態を維持します。

検証内容:
- `pnpm run <script>` 参照が `package.json` に存在すること
- markdown link と inline code のローカル file/path 参照が実在すること
- `docs/README.md` から辿れる `docs/ci/*` / `docs/quality/*` の主要ドキュメントに加え、`docs/TLA+/*` / `docs/adapters/*` / `docs/agent-builder/*` / `docs/agents/recipes/*` / `docs/architecture/*` / `docs/articles/*` / `docs/articles/zenn/*` / `docs/benchmark/*` / `docs/changes/*` / `docs/cheatsheets/*` / `docs/codex/*` / `docs/contributing/*` / `docs/ddd/*` / `docs/development/*` / `docs/examples/*` / `docs/flows/*` / `docs/getting-started/*` / `docs/guides/*` / `docs/handoff/*` / `docs/infra/*` / `docs/integrations/*` / `docs/internal/*` / `docs/legacy/**/*.md` / `docs/maintenance/*` / `docs/notes/*` / `docs/observability/*` / `docs/operate/*` / `docs/operations/*` / `docs/phases/*` / `docs/product/*` / `docs/project/*` / `docs/proposals/*` / `docs/reference/*` / `docs/research/*` / `docs/resilience/*` / `docs/roadmap/*` / `docs/samples/*` / `docs/spec/*` / `docs/strategy/*` / `docs/templates/**/*.md` / `docs/testing/*` / `docs/trace/*` / `docs/trace/grafana/*` / `docs/troubleshooting/*` / `docs/verify/*` / `docs/workflows/*` の trust-tier front matter を既定スコープで検証すること
- `docs/README.md` / `docs/ci-policy.md` に canonical な CI operation link が含まれること
- `docs/ci-policy.md` の CI reference section に重複がないこと
- `docs/agents/commands.md` が `.github/workflows/agent-commands.yml` と同期していること
- CI runbook の shell code block を `bash -n` で構文検証すること
- `docs/ci/*` の TODO/FIXME marker が Issue 参照付きであること（`TODO(#<issue>)` / `FIXME(#<issue>)`）
- governed docs の `docRole` / `canonicalSource` / `lastVerified` front matter を検証すること
- `docs/legacy/**/*.md` と `docs/notes/*.md` を archival / working-note narrative として扱い、歴史的文言や issue memo の文言に対する narrative warning を除外すること

既定の対象:
- Base: リポジトリルートの README ファイル、`docs/README.md`、および `DEFAULT_DOC_FILES` に含まれる Getting Started / Product / Integrations の主要ドキュメント
- Dynamic discovery: リポジトリルートの README ファイルと `docs/README.md` を seed にし、設定された discovery prefix の範囲でリンクされた `docs/**/*.md` を再帰的に追加スキャン

生成物参照:
- `artifacts/*` / `reports/*` は生成物参照として扱い、missing-path 判定から除外します。

### 使い方
```bash
pnpm run check:doc-consistency
```

JSON 出力:
```bash
pnpm run check:doc-consistency -- --format json
```

個別ファイル指定:
```bash
pnpm run check:doc-consistency -- --docs README.md,docs/README.md
```

注意:
- `--format json` または `--docs` を指定した場合は互換性のため `check-doc-consistency.mjs` のみを実行し、他の validator はスキップします。
- CI 索引チェックを併せて実行する場合は `pnpm run check:ci-doc-index-consistency` を別途実行します。

CI index のみ:
```bash
pnpm run check:ci-doc-index-consistency
```

Runbook command blocks のみ:
```bash
pnpm run check:runbook-command-blocks
```

Doc TODO markers のみ:
```bash
pnpm run check:doc-todo-markers
```

### 除外ルール
checker は次を意図的に無視します。
- external URL（`https://...`, `mailto:...` など）
- heading anchor（`#...`）
- wildcard / glob style entry（`*`）
- template variable（`${...}`）
- `.md` のような extension-only token

新しい docs section で追加除外が必要になった場合は、`scripts/docs/check-doc-consistency.mjs` を更新し、`tests/unit/docs/` に unit test を追加してください。

### CI 連携
`Verify Lite` と `Docs Doctest` はどちらも `check-doc-consistency-all.mjs` を実行します。これにより broken reference だけでなく、contract catalog coverage と doc governance も required lane で検出されます。
