# Agents Runbook: Formal Methods

## When to use

- 形式手法ツールチェーンの稼働確認が必要なとき
- formal関連CIのfail原因を切り分けるとき

## What to load (primary sources)

- `docs/quality/formal-runbook.md`
- `docs/quality/formal-full-run.md`
- `docs/quality/formal-csp.md`

## Commands (copy/paste)

```bash
pnpm -s run tools:formal:check
```

```bash
pnpm -s run verify:formal
```

```bash
pnpm -s run formal:summary
```

```bash
pnpm -s run spec:check:tla
```

## Artifacts to check

- `artifacts/formal/*`
- `artifacts/quality/formal-summary*`
- PRコメントのFormal Aggregateサマリ

## Escalation / follow-up

- ツール未導入/バージョン不一致は、`tools:formal:check` の結果をそのまま記録
- CI固有失敗かローカル再現可能かを分離して記録
