---
docRole: derived
canonicalSource:
- .github/workflows/spec-validation.yml
- docs/spec/context-pack.md
lastVerified: '2026-03-11'
---

# Recipe: Spec / IR / Drift

## When to use

- 仕様変更後に spec validation と codegen drift を確認したいとき

## Primary sources

- `.github/workflows/spec-validation.yml`
- `docs/spec/context-pack.md`

## Commands

```bash no-doctest
pnpm -s run spec:lint
```

```bash no-doctest
pnpm -s run spec:validate
```

```bash no-doctest
pnpm -s run spec:codegen
```

```bash no-doctest
git status --short
```

## Expected output

- spec validation が成功
- codegen後の差分意図が説明可能

## Artifacts

- `artifacts/spec/*`
- `tests/golden/snapshots/*`

## Follow-up

- 生成差分と手動編集差分を混在させない（必要ならPR分割）
