# Agents Runbook: Spec

## When to use

- 仕様ファイル変更後に整合と生成物ドリフトを確認するとき
- Spec validationの失敗を局所修正したいとき

## What to load (primary sources)

- `docs/spec/context-pack.md`
- `docs/quality/issue-requirements-traceability.md`
- `scripts/spec/*`

## Commands (copy/paste)

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

## Artifacts to check

- `artifacts/spec/*`
- `tests/golden/snapshots/*`
- PR内のCode Generation / Spec Validation結果

## Escalation / follow-up

- 仕様変更が広範囲の場合は、codegen差分と手動編集差分を分離してPRを分割
- スキーマ互換性を壊す変更は、移行方針をPR本文に明記
