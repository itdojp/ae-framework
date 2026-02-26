# Recipe: Formal Quickstart

## When to use

- formal関連ジョブの基本動作を短時間で確認したいとき

## Primary sources

- `docs/quality/formal-runbook.md`
- `docs/quality/formal-tools-setup.md`

## Commands

```bash
pnpm -s run tools:formal:check
```

```bash
pnpm -s run verify:formal
```

```bash
pnpm -s run formal:summary
```

## Expected output

- ツール導入状態が把握できる
- formal summary が生成される

## Artifacts

- `artifacts/formal/*`
- `artifacts/quality/formal-summary.json`
- `artifacts/quality/formal-summary.md`

## Follow-up

- 未導入ツールは不足一覧をそのままPRに記録し、導入Issueへ接続
