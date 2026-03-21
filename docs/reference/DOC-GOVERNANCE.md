---
docRole: ssot
lastVerified: '2026-03-21'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---

# Document Governance Front Matter

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

Define the minimum trust-tier front matter used to prevent agents and reviewers from treating narrative or convenience docs as normative SSOT.

### 2. Front Matter Fields

```yaml
---
docRole: ssot | derived | narrative
canonicalSource:
  - docs/path/to/source.md
lastVerified: YYYY-MM-DD
owner: team-or-doc-owner        # required for ssot
verificationCommand: pnpm ...   # required for ssot
---
```

### 3. Roles

- `ssot`
  - Normative document
  - Must define `owner` and `verificationCommand`
- `derived`
  - Summary, index, or guidance derived from primary sources
  - Must define `canonicalSource`
- `narrative`
  - Background, overview, onboarding, or explanatory prose
  - Normative wording is warning-worthy unless explicitly exempted

### 4. Current Coverage

The current lint target includes:

- `README.md`
- `AGENTS.md`
- `docs/README.md`
- `docs/reference/DOC-GOVERNANCE.md`
- `docs/TLA+/*.md`
- `docs/adapters/*.md`
- `docs/agent-builder/*.md`
- `docs/agents/*.md`
- `docs/agents/recipes/*.md`
- `docs/architecture/*.md`
- `docs/articles/*.md`
- `docs/articles/zenn/*.md`
- `docs/benchmark/*.md`
- `docs/changes/*.md`
- `docs/cheatsheets/*.md`
- `docs/ci/*.md`
- `docs/codex/*.md`
- `docs/contributing/*.md`
- `docs/development/*.md`
- `docs/ddd/*.md`
- `docs/examples/*.md`
- `docs/flows/*.md`
- `docs/getting-started/*.md`
- `docs/guides/*.md`
- `docs/handoff/*.md`
- `docs/infra/*.md`
- `docs/integrations/*.md`
- `docs/internal/*.md`
- `docs/legacy/**/*.md`
- `docs/maintenance/*.md`
- `docs/notes/*.md`
- `docs/observability/*.md`
- `docs/operate/*.md`
- `docs/operations/*.md`
- `docs/phases/*.md`
- `docs/product/*.md`
- `docs/proposals/*.md`
- `docs/project/*.md`
- `docs/quality/*.md`
- `docs/research/*.md`
- `docs/resilience/*.md`
- `docs/roadmap/*.md`
- `docs/reference/*.md`
- `docs/samples/*.md`
- `docs/spec/*.md`
- `docs/strategy/*.md`
- `docs/testing/*.md`
- `docs/templates/**/*.md`
- `docs/trace/*.md`
- `docs/trace/grafana/*.md`
- `docs/troubleshooting/*.md`
- `docs/verify/*.md`
- `docs/workflows/*.md`

### 5. Validation

```bash
node scripts/docs/check-doc-governance.mjs
pnpm -s run check:doc-consistency
```

When extending governance coverage to a new directory, run changed-markdown doctest after adding front matter:

```bash
DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main
```

### 6. Exemptions and Snippet Rules

- `docs/legacy/**/*.md` and `docs/notes/*.md` are treated as archival / working-note narrative.
- Front matter remains mandatory, but historical wording and issue memo phrasing are exempt from narrative-wording warnings.
- Use `text` fences by default for illustrative snippets or sample payloads.
- Keep language-tagged fences only when the language matters, and add `no-doctest` when execution should be suppressed.

## 日本語

## 1. 目的

文書ごとの trust tier を front matter で明示し、agent が narrative docs を規範文書として誤読しないようにするための最小仕様です。

## 2. Front matter fields

```yaml
---
docRole: ssot | derived | narrative
canonicalSource:
  - docs/path/to/source.md
lastVerified: YYYY-MM-DD
owner: team-or-doc-owner        # ssot のとき必須
verificationCommand: pnpm ...   # ssot のとき必須
---
```

## 3. Roles

- `ssot`: 規範文書。owner と verificationCommand を必須とする。
- `derived`: 一次情報を要約・導線化した文書。canonicalSource を必須とする。
- `narrative`: 背景説明・概要・導入文章。規範語の使用は warning 対象とする。

## 4. 現在の適用範囲

現時点の lint 対象は次です。

- `README.md`
- `AGENTS.md`
- `docs/README.md`
- `docs/reference/DOC-GOVERNANCE.md`
- `docs/TLA+/*.md`
- `docs/adapters/*.md`
- `docs/agent-builder/*.md`
- `docs/agents/*.md`
- `docs/agents/recipes/*.md`
- `docs/architecture/*.md`
- `docs/articles/*.md`
- `docs/articles/zenn/*.md`
- `docs/benchmark/*.md`
- `docs/changes/*.md`
- `docs/cheatsheets/*.md`
- `docs/ci/*.md`
- `docs/codex/*.md`
- `docs/contributing/*.md`
- `docs/development/*.md`
- `docs/ddd/*.md`
- `docs/examples/*.md`
- `docs/flows/*.md`
- `docs/getting-started/*.md`
- `docs/guides/*.md`
- `docs/handoff/*.md`
- `docs/infra/*.md`
- `docs/integrations/*.md`
- `docs/internal/*.md`
- `docs/legacy/**/*.md`
- `docs/maintenance/*.md`
- `docs/notes/*.md`
- `docs/observability/*.md`
- `docs/operate/*.md`
- `docs/operations/*.md`
- `docs/phases/*.md`
- `docs/product/*.md`
- `docs/proposals/*.md`
- `docs/project/*.md`
- `docs/quality/*.md`
- `docs/research/*.md`
- `docs/resilience/*.md`
- `docs/roadmap/*.md`
- `docs/reference/*.md`
- `docs/samples/*.md`
- `docs/spec/*.md`
- `docs/strategy/*.md`
- `docs/testing/*.md`
- `docs/templates/**/*.md`
- `docs/trace/*.md`
- `docs/trace/grafana/*.md`
- `docs/troubleshooting/*.md`
- `docs/verify/*.md`
- `docs/workflows/*.md`

## 5. Validation

```bash
node scripts/docs/check-doc-governance.mjs
pnpm -s run check:doc-consistency
```

governance 対象を新規ディレクトリへ拡張する場合は、front matter 追加後に changed-markdown doctest も実行する。

```bash
DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main
```

`docs/legacy/**/*.md` と `docs/notes/*.md` は archival / working-note narrative として扱う。front matter は必須だが、歴史的文脈や issue memo の文言を保持するため narrative wording warning の対象外とする。

説明用 snippet / 出力例 / 擬似 payload は `text` fence を基本とし、言語情報を残したい場合だけ `no-doctest` modifier を使う。
