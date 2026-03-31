---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- docs/quality/formal-csp.md
lastVerified: '2026-03-31'
---

# Agents Runbook: Formal Methods

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need to verify that the formal methods toolchain is available and consistent
- when you need to isolate the cause of a formal-related CI failure before escalating

### What to load (primary sources)
- `docs/quality/formal-runbook.md`
- `docs/quality/formal-full-run.md`
- `docs/quality/formal-csp.md`

### Commands (copy/paste)
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

### Artifacts to check
- `artifacts/formal/*`
- `artifacts/quality/formal-summary*`
- Formal Aggregate summary in the PR comment stream

### Escalation / follow-up
- when tools are missing or versions do not match, record the raw `tools:formal:check` result without paraphrasing
- record separately whether the failure is CI-only or reproducible in a local environment
- if the failure blocks required checks, attach the latest formal summary artifact before requesting review help

## 日本語

### When to use
- 形式手法ツールチェーンの稼働確認が必要なとき
- formal 関連 CI の fail 原因を切り分けるとき

### What to load (primary sources)
- `docs/quality/formal-runbook.md`
- `docs/quality/formal-full-run.md`
- `docs/quality/formal-csp.md`

### Commands (copy/paste)
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

### Artifacts to check
- `artifacts/formal/*`
- `artifacts/quality/formal-summary*`
- PR comment stream 上の Formal Aggregate summary

### Escalation / follow-up
- ツール未導入やバージョン不一致は、`tools:formal:check` の生出力をそのまま記録する
- CI 固有失敗かローカル再現可能かを分離して記録する
- required checks を block する failure では、review 依頼前に最新の formal summary artifact を添付する
