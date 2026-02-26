# Agents Runbook: Context Pack

## When to use

- Context Packの構造検証やPhase5+検証を実行するとき
- Context Pack関連のCI失敗を修復するとき

## What to load (primary sources)

- `docs/spec/context-pack.md`
- `docs/guides/context-pack-onboarding-checklist.md`
- `docs/operations/context-pack-troubleshooting.md`

## Commands (copy/paste)

```bash
pnpm -s run context-pack:validate
```

```bash
pnpm -s run context-pack:verify-phase5
```

```bash
pnpm -s run context-pack:verify-functor
```

```bash
pnpm -s run context-pack:verify-natural-transformation
```

## Artifacts to check

- `artifacts/context-pack/*`
- `artifacts/quality/context-pack*`
- CIの`context-pack-e2e` / context-pack関連ジョブ結果

## Escalation / follow-up

- モデル境界の修正が必要な場合は、対象specと生成物を同時に更新
- 自動修復系（suggest/patch）検討は #2290 の方針に従う
