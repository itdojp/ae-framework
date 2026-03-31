---
docRole: derived
canonicalSource:
- .github/workflows/spec-validation.yml
- docs/spec/context-pack.md
- docs/agents/spec.md
lastVerified: '2026-03-31'
---

# Recipe: Spec / IR / Drift

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need a focused replay after changing spec files
- when you need to confirm whether a failure comes from spec validation or generated drift
- when you need to separate generated diffs from manual edits before review

### What to load (primary sources)
- `.github/workflows/spec-validation.yml`
- `docs/spec/context-pack.md`
- `docs/agents/spec.md`

### Commands (copy/paste)
Start from lint and validation, then regenerate and inspect the resulting file delta.

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

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

### Expected output
- spec validation succeeds before you reason about codegen drift
- generated diffs can be explained from the spec change rather than from unrelated local noise
- the PR record can distinguish generated changes from manual edits

### Artifacts to check
- `artifacts/spec/*`
- `tests/golden/snapshots/*`
- PR results for Spec Validation and Code Generation related jobs

### First checks to perform
- confirm whether `spec:validate` or `spec:codegen` is the first failing step before editing source files
- after `spec:codegen`, inspect `git status --short` and separate generated outputs from handwritten files immediately
- if required checks are red while local commands are green, compare the required-check URL, branch freshness, and latest head SHA before changing the spec again

### Follow-up
- do not mix generated diffs and manual edits when the scope can be split into separate PRs
- if the drift touches unrelated paths, identify the generating source before cleanup
- escalate to `docs/agents/spec.md` when the failure scope expands beyond the quick recipe path

## 日本語

### When to use
- spec file 変更後に、focused な再確認をしたいとき
- failure が spec validation 由来か generated drift 由来かを切り分けたいとき
- review 前に、生成差分と手動編集差分を分離したいとき

### What to load (primary sources)
- `.github/workflows/spec-validation.yml`
- `docs/spec/context-pack.md`
- `docs/agents/spec.md`

### Commands (copy/paste)
まず lint と validation を実行し、その後で再生成と差分確認を行います。

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

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

### Expected output
- codegen drift を議論する前に spec validation の成功可否を確認できる
- 生成差分が、無関係なローカルノイズではなく spec 変更に起因することを説明できる
- PR 上で generated changes と manual edits を区別して記録できる

### Artifacts to check
- `artifacts/spec/*`
- `tests/golden/snapshots/*`
- PR 上の Spec Validation / Code Generation 関連 job 結果

### First checks to perform
- source file を編集する前に、最初の failing step が `spec:validate` か `spec:codegen` かを確認する
- `spec:codegen` 後はすぐに `git status --short` を確認し、generated output と handwritten file を分離する
- required checks が red でローカル command が green の場合は、spec を再変更する前に required-check URL、branch freshness、最新 head SHA を照合する

### Follow-up
- 分割できる範囲なら、generated diff と manual edit を同じ PR に混在させない
- drift が無関係な path に及ぶ場合は、cleanup の前に生成元を特定する
- recipe の範囲を越える場合は `docs/agents/spec.md` へ escalation する
