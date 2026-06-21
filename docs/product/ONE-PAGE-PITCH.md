---
docRole: derived
canonicalSource:
- docs/product/LAUNCH-KIT.md
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/product/DOGFOODING-REPORT-2026Q3.md
lastVerified: '2026-06-21'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# One-Page Pitch: Bring Your Own Agent. Keep Your Assurance Plane.

> Language / 言語: English | 日本語

## English

### The problem

Coding-agent output is easy to produce but hard to trust at merge time. Teams use
Codex, Claude Code, GitHub Copilot, CI bots, formal tools, and human reviewers,
but the evidence needed for release judgment often stays scattered across raw
logs, comments, local notes, and workflow checks.

### The product thesis

**Bring your own agent. Keep your assurance plane.** ae-framework keeps the
judgment layer stable while producers remain replaceable.

### What ae-framework adds

- **Producer-neutral evidence boundary:** agent, human, CI, and formal-tool output
  enters as evidence input, not as approval.
- **Reviewer-ready artifacts:** producer summaries, assurance summaries, claim
  manifests, policy-gate summaries, and PR review Markdown show what is supported,
  missing, waived, or out of scope.
- **Risk-aware escalation:** routine PRs stay fast; selected high-risk claims can
  demand stronger evidence, waivers, or blocking policy decisions.

### Preview evidence

Internal dogfooding on PR #3516 through PR #3521 reached merge with 22 review
threads resolved and 0 unresolved review threads at final review-completeness
checks. The demos show 2 scope-drift findings and 2 selected high-risk claims in
fixture-backed, repeatable scenarios. These are traceability observations, not a
speed benchmark.

### Try it

```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install --frozen-lockfile
pnpm run demo:agent-assurance
```

Open `artifacts/review/agent-assurance-demo/assurance-review.md`, then read:

- `docs/product/DEMO-SCRIPT.md`
- `docs/guides/byo-agent-assurance-quickstart.md`
- `docs/product/DOGFOODING-REPORT-2026Q3.md`

### Non-goals

This preview is not an agent runtime, hosted service, auto-merge guarantee,
agent-vendor benchmark, or all-PR formal-proof mandate.

## 日本語

### 課題

coding agent の output は生成しやすい一方、merge 判断時に信頼できる evidence へ整理するのが難しい。
Codex、Claude Code、GitHub Copilot、CI bot、formal tool、人間 reviewer が混在すると、release
judgment に必要な情報が raw log、comment、local note、workflow check に分散しやすい。

### 提案

**Bring your own agent. Keep your assurance plane.** ae-framework は producer を交換可能にしつつ、
judgment layer を安定させる。

### 提供価値

- agent / human / CI / formal output を approval ではなく evidence input として扱う。
- producer summary、assurance summary、claim manifest、policy-gate summary、PR review Markdown で
  supported / missing / waived / out-of-scope を確認できる。
- 通常 PR は fast lane に留め、selected high-risk claim だけ stronger evidence や waiver を要求できる。

### 試す手順

`pnpm run demo:agent-assurance` を実行し、`artifacts/review/agent-assurance-demo/assurance-review.md` を開く。
続いて `docs/product/DEMO-SCRIPT.md` と `docs/product/DOGFOODING-REPORT-2026Q3.md` を確認する。
