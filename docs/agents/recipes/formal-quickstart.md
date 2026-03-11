---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- docs/quality/formal-tools-setup.md
lastVerified: '2026-03-11'
---

# Recipe: Formal Quickstart

## When to use

- formal関連ジョブの基本動作を短時間で確認したいとき

## Primary sources

- `docs/quality/formal-runbook.md`
- `docs/quality/formal-tools-setup.md`

## Commands

```bash no-doctest
pnpm -s run tools:formal:check
```

```bash no-doctest
pnpm -s run verify:formal
```

```bash no-doctest
pnpm -s run formal:summary
```

## Expected output

- ツール導入状態が把握できる
- formal summary が生成される

## Artifacts

- `artifacts/hermetic-reports/formal/summary.json`
- `artifacts/hermetic-reports/formal/*-summary.json`
- `artifacts/hermetic-reports/formal/*-output.txt`

## Follow-up

- 未導入ツールは不足一覧をそのままPRに記録し、導入Issueへ接続
