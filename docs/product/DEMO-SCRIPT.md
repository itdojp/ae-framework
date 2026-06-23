---
docRole: derived
canonicalSource:
- docs/product/LAUNCH-KIT.md
- docs/guides/byo-agent-assurance-quickstart.md
- examples/assurance-control-plane/agent-assurance-demo/README.md
- examples/assurance-control-plane/scope-drift-demo/README.md
- examples/assurance-control-plane/high-risk-escalation-demo/README.md
lastVerified: '2026-06-21'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Demo Script: Agent-Neutral Assurance Control Plane Preview

> Language / 言語: English | 日本語

## English

### 5-minute live script

| Time | Speaker action | Show |
| --- | --- | --- |
| 0:00-0:30 | State the thesis: "Bring your own agent. Keep your assurance plane." | `docs/product/ONE-PAGE-PITCH.md` |
| 0:30-1:15 | Explain producer boundary: agents, humans, CI, and formal tools produce evidence input, not approvals. | `docs/agents/evidence-adapters.md` and `fixtures/agents/evidence-adapters/` |
| 1:15-2:15 | Run or open the offline demo output. | `pnpm run demo:agent-assurance` then `artifacts/review/agent-assurance-demo/assurance-review.md` |
| 2:15-3:00 | Walk the reviewer surface: producer summary, missing evidence, assurance summary, policy interpretation. | `artifacts/review/agent-assurance-demo/assurance-review.md` |
| 3:00-3:30 | Preview the PR comment surface without posting. | `pnpm run assurance:post-review-surface -- --repo itdojp/ae-framework --pr 123 --body-file artifacts/review/agent-assurance-demo/assurance-review.md` |
| 3:30-4:00 | Show optional risk surfaces. | `examples/assurance-control-plane/scope-drift-demo/` and `examples/assurance-control-plane/high-risk-escalation-demo/` |
| 4:00-5:00 | Close with dogfooding evidence and limitations. | `docs/product/DOGFOODING-REPORT-2026Q3.md` |

### Commands

```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install --frozen-lockfile
pnpm run demo:agent-assurance
pnpm run assurance:post-review-surface -- \
  --repo itdojp/ae-framework \
  --pr 123 \
  --body-file artifacts/review/agent-assurance-demo/assurance-review.md
```

Optional scenario commands:

```bash
node scripts/demo/run-scope-drift-demo.mjs
node scripts/demo/run-high-risk-escalation-demo.mjs
```

The `ci/demo-smoke` lane in `.github/workflows/demo-smoke.yml` uses this same
representative command sequence and then runs the artifact/schema checker:

```bash
pnpm run demo:agent-assurance
node scripts/demo/run-scope-drift-demo.mjs
node scripts/demo/run-high-risk-escalation-demo.mjs
pnpm run demo:smoke:check
```

For pull requests, treat `ci/demo-smoke` as report-only and non-required until
runtime and false-positive rate are reviewed. It is enforcing on `main` push and
manual `workflow_dispatch` runs.

### Talk track

1. "ae-framework is not trying to be the coding agent. It keeps the assurance
   plane stable around whichever producer you use."
2. "This first surface is not raw logs. It is a reviewer-oriented summary of
   producer output, missing evidence, assurance status, and policy context."
3. "A normal lane can keep drift report-only; a strict high-risk lane can block
   on the same evidence when policy selects stronger assurance."
4. "The dogfooding report shows traceability evidence from ae-framework PRs, but
   it is not a benchmark and not an agent-vendor comparison."

### Backup plan

If local setup is unavailable, use checked-in documentation and fixtures only:

1. Open `examples/assurance-control-plane/agent-assurance-demo/README.md`.
2. Open `docs/guides/byo-agent-assurance-quickstart.md`.
3. Open `docs/product/DOGFOODING-REPORT-2026Q3.md`.
4. Explain the architecture from `docs/product/LAUNCH-KIT.md`.

### Presenter checklist

- Do not claim unmeasured review-speed improvement.
- Do not claim agent-vendor superiority.
- Do not imply auto-merge or formal proof for every PR.
- Keep the PR posting helper in dry-run mode unless you are intentionally posting with `gh pr comment`.
- State that the preview is fixture-backed and offline unless running against a live PR.
- End with the next step: run the 15-minute quickstart and inspect the review Markdown.

## 日本語

### 5分 demo

1. `Bring your own agent. Keep your assurance plane.` を一文で説明する。
2. agent / human / CI / formal tool は approval ではなく evidence producer であると説明する。
3. `pnpm run demo:agent-assurance` を実行し、`artifacts/review/agent-assurance-demo/assurance-review.md` を開く。
4. missing evidence、assurance summary、policy interpretation の順に reviewer surface を見る。
5. `pnpm run assurance:post-review-surface -- --repo itdojp/ae-framework --pr 123 --body-file artifacts/review/agent-assurance-demo/assurance-review.md` を dry-run で実行し、PR comment surface を確認する。
6. scope drift / high-risk escalation の optional scenario を示す。
7. dogfooding report の観測値と limitations を示し、benchmark ではないことを明確にする。

### CI smoke lane

`.github/workflows/demo-smoke.yml` の `ci/demo-smoke` は、上記と同じ代表 command sequence に
artifact/schema checker を加えて実行します。

```bash
pnpm run demo:agent-assurance
node scripts/demo/run-scope-drift-demo.mjs
node scripts/demo/run-high-risk-escalation-demo.mjs
pnpm run demo:smoke:check
```

PR では report-only / non-required として扱い、runtime と false-positive rate を確認するまでは
required check にしません。`main` push と manual `workflow_dispatch` では enforcing です。

### 予備手順

local setup が使えない場合は、`docs/product/ONE-PAGE-PITCH.md`、`docs/product/LAUNCH-KIT.md`、
`docs/guides/byo-agent-assurance-quickstart.md`、`docs/product/DOGFOODING-REPORT-2026Q3.md` を順に開いて説明する。
