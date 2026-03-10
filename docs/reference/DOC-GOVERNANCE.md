---
docRole: ssot
lastVerified: '2026-03-10'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---

# Document Governance Front Matter

> Language / 言語: English | 日本語

---

## English (Summary)

This document defines the trust-tier front matter used to mark whether a document is an SSOT, a derived guide, or a narrative explanation.

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
- `docs/agents/*.md`
- `docs/getting-started/*.md`
- `docs/guides/*.md`
- `docs/integrations/*.md`
- `docs/operate/*.md`
- `docs/product/*.md`
- `docs/project/*.md`
- `docs/quality/*.md`

## 5. Validation

```bash
node scripts/docs/check-doc-governance.mjs
pnpm -s run check:doc-consistency
```
