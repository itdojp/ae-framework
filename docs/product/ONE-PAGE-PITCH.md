---
docRole: derived
canonicalSource:
- docs/product/LAUNCH-KIT.md
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/product/DOGFOODING-REPORT-2026Q3.md
- docs/product/PILOT-REPORT-2026Q3-01.md
- docs/product/CONTROLLED-COMPARISON-PROTOCOL.md
- docs/product/EFFECTIVENESS-METRICS.md
lastVerified: '2026-06-23'
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

Pilot evidence is separate from internal dogfooding. The current ACP-097 pilot
report is `dry-run only` and records 0 live external PRs collected, so it
supports pilot readiness, consent/redaction boundaries, and report-only metric
vocabulary rather than live effectiveness. The controlled-comparison protocol is
prepared but not executed; review-speed, safety, adoption-impact, and
agent-vendor superiority claims remain out of scope until comparable baseline
data exists.

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
- `docs/product/PILOT-REPORT-2026Q3-01.md`
- `docs/product/DOGFOODING-REPORT-2026Q3.md`
- `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md`

### Non-goals

This preview is not an agent runtime, hosted service, auto-merge guarantee,
agent-vendor benchmark, review-speed benchmark, safety benchmark, adoption-impact
claim, or all-PR formal-proof mandate.

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

### Preview evidence

internal dogfooding では PR #3516〜#3521 が merge され、final review-completeness で review thread 22件解決、未解決0件を確認した。これは review traceability の観測であり、speed benchmark ではない。

ACP-097 pilot report は `dry-run only` で live external PR の収集は0件である。pilot readiness、consent/redaction boundary、report-only metrics vocabulary は説明できるが、live effectiveness、review-speed、安全性、導入効果は主張しない。controlled-comparison protocol は準備済みだが未実施であり、comparable baseline data が得られるまで benchmark claim は扱わない。

### 試す手順

`pnpm run demo:agent-assurance` を実行し、`artifacts/review/agent-assurance-demo/assurance-review.md` を開く。
続いて `docs/product/DEMO-SCRIPT.md`、`docs/guides/byo-agent-assurance-quickstart.md`、`docs/product/PILOT-REPORT-2026Q3-01.md`、`docs/product/DOGFOODING-REPORT-2026Q3.md`、`docs/product/CONTROLLED-COMPARISON-PROTOCOL.md` を確認する。

### 主張しないこと

agent runtime、hosted service、auto-merge guarantee、agent-vendor benchmark、review-speed benchmark、安全性benchmark、導入効果claim、all-PR formal-proof mandate ではない。
