---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- docs/quality/formal-tools-setup.md
- docs/agents/formal.md
lastVerified: '2026-03-31'
---

# Recipe: Formal Quickstart

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need a low-friction first pass for formal-related CI failures
- when you need to confirm whether the formal toolchain is present before escalating
- when you need the shortest operator path to a usable formal summary artifact

### What to load (primary sources)
- `docs/quality/formal-runbook.md`
- `docs/quality/formal-tools-setup.md`
- `docs/agents/formal.md`

### Commands (copy/paste)
Start with tool availability, then run the narrow formal baseline and summarize the result.

```bash no-doctest
pnpm -s run tools:formal:check
```

```bash no-doctest
pnpm -s run verify:formal
```

```bash no-doctest
pnpm -s run formal:summary
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

### Expected output
- tool availability or version gaps are identified before deeper debugging
- `verify:formal` completes with enough signal to distinguish tool absence from a real verification failure
- a formal summary artifact is available for PR evidence or escalation

### Artifacts to check
- `artifacts/formal/formal-summary-v1.json`
- `artifacts/formal/formal-summary-v2.json`
- `artifacts/hermetic-reports/formal/summary.json`
- `artifacts/hermetic-reports/formal/*-output.txt`
- the Formal Aggregate summary in the PR comment stream when CI has already run

### First checks to perform
- inspect the raw output of `pnpm -s run tools:formal:check` before changing code or workflow configuration
- in the aggregate summary, separate tool-not-available states from verification failures before escalating
- if required checks are blocked in GitHub but local formal commands are green, compare the latest required-check URL with the PR head SHA and branch freshness

### Follow-up
- when tools are missing, record the missing binaries or jar paths exactly and link the setup action to `docs/quality/formal-tools-setup.md`
- when the failure is reproducible locally, attach the latest formal summary artifact and the first relevant `*-output.txt` log path to the PR
- when the problem expands beyond the quickstart path, escalate to `docs/quality/formal-runbook.md` or `docs/agents/formal.md`

## 日本語

### When to use
- formal 関連 CI の fail を低コストで最初に切り分けたいとき
- escalation 前に、formal toolchain の有無を確認したいとき
- PR 証跡や追加調査に使う formal summary artifact を最短で取得したいとき

### What to load (primary sources)
- `docs/quality/formal-runbook.md`
- `docs/quality/formal-tools-setup.md`
- `docs/agents/formal.md`

### Commands (copy/paste)
まず tool availability を確認し、その後で最小の formal baseline を実行し、summary を生成します。

```bash no-doctest
pnpm -s run tools:formal:check
```

```bash no-doctest
pnpm -s run verify:formal
```

```bash no-doctest
pnpm -s run formal:summary
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

### Expected output
- 深掘り前に、ツール有無やバージョン差異を切り分けられる
- `verify:formal` の結果から、ツール未導入と実際の verification failure を区別できる
- PR 証跡や escalation に使える formal summary artifact を取得できる

### Artifacts to check
- `artifacts/formal/formal-summary-v1.json`
- `artifacts/formal/formal-summary-v2.json`
- `artifacts/hermetic-reports/formal/summary.json`
- `artifacts/hermetic-reports/formal/*-output.txt`
- CI 実行済みなら PR comment stream 上の Formal Aggregate summary

### First checks to perform
- コードや workflow 設定を変更する前に、`pnpm -s run tools:formal:check` の生出力を確認する
- aggregate summary では、verification failure と tool-not-available を分けて判断してから escalation する
- GitHub の required checks だけが block していてローカル formal command が green の場合は、required-check URL、PR head SHA、branch freshness を先に照合する

### Follow-up
- ツール不足時は、欠けている binary や jar path をそのまま記録し、`docs/quality/formal-tools-setup.md` の該当 setup action へ接続する
- ローカル再現できる failure では、最新 formal summary artifact と最初に確認すべき `*-output.txt` の log path を PR に添付する
- quickstart の範囲を越える場合は、`docs/quality/formal-runbook.md` または `docs/agents/formal.md` へ escalation する
