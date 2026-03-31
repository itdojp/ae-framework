---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/quality/issue-requirements-traceability.md
lastVerified: '2026-03-31'
---

# Agents Runbook: Spec

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need to verify consistency and code generation drift after changing spec files
- when you need to fix a spec validation failure with the smallest possible local scope

### What to load (primary sources)
- `docs/spec/context-pack.md`
- `docs/quality/issue-requirements-traceability.md`
- `scripts/spec/*`
- `.github/workflows/spec-validation.yml`

### Commands (copy/paste)
```bash
pnpm -s run spec:lint
```

```bash
pnpm -s run spec:validate
```

```bash
pnpm -s run validate:specs:ci
```

```bash
pnpm -s run spec:codegen
```

### Artifacts to check
- `artifacts/spec/*`
- `tests/golden/snapshots/*`
- PR results for Spec Validation and Code Generation

### Escalation / follow-up
- if the spec change is broad, split generated diffs and manual edits into separate PRs when possible
- if the change breaks schema compatibility, record the migration path in the PR body before requesting review
- if `spec:codegen` rewrites unrelated files, identify the generating source first and avoid mixing drift cleanup with semantic changes

## 日本語

### When to use
- spec file 変更後に整合性と code generation drift を確認したいとき
- Spec validation の失敗を最小の局所修正で直したいとき

### What to load (primary sources)
- `docs/spec/context-pack.md`
- `docs/quality/issue-requirements-traceability.md`
- `scripts/spec/*`
- `.github/workflows/spec-validation.yml`

### Commands (copy/paste)
```bash
pnpm -s run spec:lint
```

```bash
pnpm -s run spec:validate
```

```bash
pnpm -s run validate:specs:ci
```

```bash
pnpm -s run spec:codegen
```

### Artifacts to check
- `artifacts/spec/*`
- `tests/golden/snapshots/*`
- PR 上の Spec Validation と Code Generation の結果

### Escalation / follow-up
- spec 変更が広範囲な場合は、生成差分と手動編集差分を可能な限り PR 分割する
- schema compatibility を壊す変更は、review 依頼前に移行方針を PR 本文へ明記する
- `spec:codegen` が無関係なファイルまで書き換える場合は、まず生成元を特定し、drift cleanup と意味変更を混在させない
